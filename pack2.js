// pack2.js — Pack2: serializador binario compacto y fiel para objetos JavaScript.
//
//   import Pack2 from './pack2.js';          // también: import { Pack2 } from './pack2.js'
//
//   const bytes = Pack2.encode(obj);          // Uint8Array
//   const copia = Pack2.decode(bytes);        // objeto equivalente al original
//
//   const gz = await Pack2.encodeCompressed(obj);       // codifica + gzip (CompressionStream)
//   const otra = await Pack2.decodeCompressed(gz);
//
// Qué guarda con fidelidad (además de lo que entiende JSON):
//   undefined, NaN, ±Infinity, -0, BigInt, Date, RegExp, Error, Map, Set, ArrayBuffer,
//   typed arrays, arrays con huecos, strings con sustitutos sueltos, referencias compartidas
//   y circulares (se conserva la identidad de los objetos).
// Qué NO conserva: prototipos de clases (una instancia vuelve como objeto plano), propiedades
//   no enumerables o de Symbol, ni lastIndex de RegExp. Funciones, Symbol, WeakMap, WeakSet,
//   Promise y DataView lanzan TypeError (no se pierden en silencio).
//
// Cómo ahorra bytes: tabla de strings (claves y strings repetidos), varints, enteros chicos
// en el propio tag, decimales como entero escalado, arrays numéricos empaquetados (con delta),
// y formato columnar para arrays de objetos parecidos (incluye campos opcionales).
// Los typed arrays se guardan en el orden de bytes de la plataforma (little-endian en la práctica).

const MAGIC = 0xB3;

const TAG = Object.freeze({
  NULL: 0, FALSE: 1, TRUE: 2, UINT: 3, NINT: 4, F32: 5, F64: 6, STR: 7, REF: 8, ARR: 9, OBJ: 10,
  AINT: 11, ADELTA: 12, AF32: 13, AF64: 14, DEC: 15, COLS: 16, ABOOL: 17, AENUM: 18,
  UNDEF: 19, WSTR: 20, BIGINT: 21, DATE: 22, MAP: 23, SET: 24, TYPED: 25, ABUF: 26, REGEXP: 27,
  ERROR: 28, HOLE: 29, OBJDEF: 30, OBJREF: 31,
});
// 0x20..0x3F string corto (largo en el tag) | 0x40..0x5F ref a la tabla 0..31
// 0x60..0x6F array de 0..15 | 0x70..0x7F objeto de 0..15 | 0x80..0xFF entero 0..127
const SSTR = 0x20, SREF = 0x40, SARR = 0x60, SOBJ = 0x70;

const OP = Object.prototype;
const MAXP = 2 ** 50;          // |entero| máximo para zigzag/delta exactos
const MINROWS = 4;             // filas mínimas para pasar a columnar
const MAXCOLS = 64;            // columnas máximas en el formato columnar
const POW = [1, 1e1, 1e2, 1e3, 1e4, 1e5, 1e6, 1e7, 1e8, 1e9];
const TYPED = [Int8Array, Uint8Array, Uint8ClampedArray, Int16Array, Uint16Array, Int32Array, Uint32Array,
               Float32Array, Float64Array, BigInt64Array, BigUint64Array];
const ERRORS = { Error, TypeError, RangeError, SyntaxError, ReferenceError, EvalError, URIError };
const HOLE = Symbol('hueco');
const enc = new TextEncoder();
const dec = new TextDecoder();
let scratch = new Float64Array(1024);

const vlen = n => n < 128 ? 1 : n < 16384 ? 2 : n < 2097152 ? 3 : n < 268435456 ? 4 : n < 34359738368 ? 5 :
                  n < 4398046511104 ? 6 : n < 562949953421312 ? 7 : 8;
const zz = x => (x >= 0 ? x * 2 : -x * 2 - 1);
const unzz = z => (z % 2 === 0 ? z / 2 : -(z + 1) / 2);
const okAt = (x, k) => { const m = Math.round(x * POW[k]); return m <= MAXP && m >= -MAXP && m / POW[k] === x; };

// menor escala k (1..9) con la que x se guarda exacto como entero escalado, o -1
function scaleScalar(x) {
  const ax = x < 0 ? -x : x;
  if (ax < 1e6 && !okAt(x, 9)) return -1;      // si no entra con 9 decimales, no entra con ninguno (para |x| < 1e6)
  for (let k = 1; k <= 9; k++) if (okAt(x, k)) return k;
  return -1;
}

function wellFormed(s) {
  if (typeof s.isWellFormed === 'function') return s.isWellFormed();
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c >= 0xD800 && c <= 0xDBFF) {
      const d = s.charCodeAt(i + 1);
      if (d >= 0xDC00 && d <= 0xDFFF) i++; else return false;
    } else if (c >= 0xDC00 && c <= 0xDFFF) return false;
  }
  return true;
}

function utf16Bytes(s) {
  const u = new Uint8Array(s.length * 2), dv = new DataView(u.buffer);
  for (let i = 0; i < s.length; i++) dv.setUint16(i * 2, s.charCodeAt(i), true);
  return u;
}

class Writer {
  constructor(cap = 1 << 16) { this.b = new Uint8Array(cap); this.dv = new DataView(this.b.buffer); this.n = 0; }
  grow(k) {
    let cap = this.b.length * 2; while (cap < this.n + k) cap *= 2;
    const nb = new Uint8Array(cap); nb.set(this.b); this.b = nb; this.dv = new DataView(nb.buffer);
  }
  need(k) { if (this.n + k > this.b.length) this.grow(k); }
  u8(x) { if (this.n >= this.b.length) this.grow(1); this.b[this.n++] = x; }
  varint(x) {
    if (x < 128) { if (this.n >= this.b.length) this.grow(1); this.b[this.n++] = x; return; }
    this.need(8);
    while (x >= 128) { this.b[this.n++] = (x % 128) | 128; x = Math.floor(x / 128); }
    this.b[this.n++] = x;
  }
  f32(x) { this.need(4); this.dv.setFloat32(this.n, x, true); this.n += 4; }
  f64(x) { this.need(8); this.dv.setFloat64(this.n, x, true); this.n += 8; }
  bytes(u) { this.need(u.length); this.b.set(u, this.n); this.n += u.length; }
  out() { return this.b.slice(0, this.n); }
}

class Encoder {
  constructor(opts) {
    this.fuse = opts.fuse !== false;
    this.columnar = opts.columnar !== false;
    this.packed = opts.packed !== false;
    this.refs = opts.refs !== false;
    this.w = new Writer();
    this.idx = new Map();
    this.tbl = [];
    this.counts = new Map();
    this.keySet = new Set();
    this.dups = null;          // objetos alcanzables por más de un camino (compartidos o circulares)
    this.ids = null;
    this.tableEnd = 0;
  }

  run(root) {
    this.scan(root);
    this.buildTable();
    const w = this.w;
    w.u8(MAGIC); w.varint(this.tbl.length);
    for (const t of this.tbl) { w.varint(t.u.length * 2 + (t.wide ? 1 : 0)); w.bytes(t.u); }
    this.tableEnd = w.n;
    if (this.dups !== null) this.ids = new Map();
    this.write(root);
    return w.out();
  }

  // ---- pasada 1: contar claves y strings, y detectar objetos repetidos
  scan(root) {
    const counts = this.counts, keySet = this.keySet, seen = this.refs ? new Set() : null;
    let dups = null;
    const plain = v => {
      const ks = Object.keys(v);
      for (let i = 0; i < ks.length; i++) {
        const k = ks[i];
        counts.set(k, (counts.get(k) || 0) + 1); keySet.add(k);
        walk(v[k]);
      }
    };
    const walk = v => {
      if (typeof v === 'string') { counts.set(v, (counts.get(v) || 0) + 1); return; }
      if (v === null || typeof v !== 'object') return;
      if (seen !== null) {
        if (seen.has(v)) { (dups ||= new Set()).add(v); return; }
        seen.add(v);
      }
      if (Array.isArray(v)) { for (let i = 0; i < v.length; i++) walk(v[i]); return; }
      if (Object.getPrototypeOf(v) === OP) return plain(v);
      if (v instanceof Map) { for (const [k, x] of v) { walk(k); walk(x); } return; }
      if (v instanceof Set) { for (const x of v) walk(x); return; }
      if (v instanceof Date || v instanceof RegExp || v instanceof Error || v instanceof ArrayBuffer || ArrayBuffer.isView(v)) return;
      plain(v);
    };
    walk(root);
    this.dups = dups;
  }

  // ---- tabla de strings: todas las claves + strings-valor que convenga deduplicar
  buildTable() {
    const fuse = this.fuse, cand = [];
    for (const [s, c] of this.counts) {
      const isKey = this.keySet.has(s);
      if (!isKey && c < 2) continue;
      const wide = !wellFormed(s), u = wide ? utf16Bytes(s) : enc.encode(s);
      if (!isKey) {
        const inline = c * ((fuse && u.length < 32 ? 0 : vlen(u.length)) + 1 + u.length);
        const table = vlen(u.length * 2) + u.length + c * (fuse ? 1.5 : 3);
        if (table >= inline) continue;
      }
      cand.push([s, c, u, wide]);
    }
    cand.sort((a, b) => b[1] - a[1]);          // los más frecuentes quedan con índice chico (1 byte)
    cand.forEach(([s, , u, wide], i) => { this.idx.set(s, i); this.tbl.push({ u, wide }); });
  }

  // ---- pasada 2: escribir
  write(v) {
    switch (typeof v) {
      case 'number': return this.num(v);
      case 'string': return this.str(v);
      case 'boolean': return this.w.u8(v ? TAG.TRUE : TAG.FALSE);
      case 'undefined': return this.w.u8(TAG.UNDEF);
      case 'bigint': return this.bigint(v);
      case 'object': break;
      default: throw new TypeError(`Pack2: no se puede serializar un valor de tipo ${typeof v}`);
    }
    if (v === null) return this.w.u8(TAG.NULL);
    if (this.dups !== null && this.dups.has(v)) {
      const id = this.ids.get(v);
      if (id !== undefined) { this.w.u8(TAG.OBJREF); return this.w.varint(id); }
      this.ids.set(v, this.ids.size);
      this.w.u8(TAG.OBJDEF);                   // "el próximo objeto se va a referenciar después"
    }
    if (Array.isArray(v)) return this.array(v);
    if (Object.getPrototypeOf(v) === OP) return this.object(v);
    return this.special(v);
  }

  object(v) {
    const w = this.w, ks = Object.keys(v), n = ks.length, idx = this.idx;
    if (this.fuse && n < 16) w.u8(SOBJ | n); else { w.u8(TAG.OBJ); w.varint(n); }
    for (let i = 0; i < n; i++) { w.varint(idx.get(ks[i])); this.write(v[ks[i]]); }
  }

  special(v) {
    const w = this.w;
    if (v instanceof Date) { w.u8(TAG.DATE); return w.f64(v.getTime()); }
    if (v instanceof Map) {
      w.u8(TAG.MAP); w.varint(v.size);
      for (const [k, x] of v) { this.write(k); this.write(x); }
      return;
    }
    if (v instanceof Set) {
      w.u8(TAG.SET); w.varint(v.size);
      for (const x of v) this.write(x);
      return;
    }
    if (ArrayBuffer.isView(v)) {
      for (let i = 0; i < TYPED.length; i++) {
        if (v instanceof TYPED[i]) {
          w.u8(TAG.TYPED); w.u8(i); w.varint(v.byteLength);
          return w.bytes(new Uint8Array(v.buffer, v.byteOffset, v.byteLength));
        }
      }
      throw new TypeError('Pack2: DataView no está soportado');
    }
    if (v instanceof ArrayBuffer) { w.u8(TAG.ABUF); w.varint(v.byteLength); return w.bytes(new Uint8Array(v)); }
    if (v instanceof RegExp) { w.u8(TAG.REGEXP); this.str(v.source); return this.str(v.flags); }
    if (v instanceof Error) {
      w.u8(TAG.ERROR); this.str(String(v.name)); this.str(String(v.message));
      return this.str(typeof v.stack === 'string' ? v.stack : '');
    }
    if (v instanceof Number || v instanceof String || v instanceof Boolean) return this.write(v.valueOf());
    if (v instanceof WeakMap || v instanceof WeakSet || v instanceof Promise ||
        (typeof SharedArrayBuffer !== 'undefined' && v instanceof SharedArrayBuffer) ||
        (typeof WeakRef !== 'undefined' && v instanceof WeakRef)) {
      throw new TypeError(`Pack2: no se puede serializar ${Object.prototype.toString.call(v)}`);
    }
    return this.object(v);                     // instancia de clase u objeto sin prototipo: se guarda como objeto plano
  }

  bigint(v) {
    const w = this.w, neg = v < 0n, hex = (neg ? -v : v).toString(16), h = hex.length % 2 ? '0' + hex : hex, n = h.length / 2;
    w.u8(TAG.BIGINT); w.u8(neg ? 1 : 0); w.varint(n); w.need(n);
    for (let i = 0; i < n; i++) w.b[w.n + i] = parseInt(h.substr(2 * i, 2), 16);
    w.n += n;
  }

  num(n) {
    const w = this.w;
    if (Number.isSafeInteger(n)) {
      if (n >= 0) {
        if (n < 128) {
          if (n === 0 && 1 / n < 0) { w.u8(TAG.F64); return w.f64(-0); }
          return w.u8(0x80 | n);
        }
        w.u8(TAG.UINT); return w.varint(n);
      }
      w.u8(TAG.NINT); return w.varint(-n);
    }
    const k = scaleScalar(n), f32 = Math.fround(n) === n;
    if (k > 0) {
      const m = Math.round(n * POW[k]);
      if (2 + vlen(zz(m)) < (f32 ? 5 : 9)) { w.u8(TAG.DEC); w.u8(k); return w.varint(zz(m)); }
    }
    if (f32) { w.u8(TAG.F32); return w.f32(n); }
    w.u8(TAG.F64); w.f64(n);
  }

  str(s) {
    const i = this.idx.get(s);
    if (i !== undefined) {
      if (this.fuse && i < 32) return this.w.u8(SREF | i);
      this.w.u8(TAG.REF); return this.w.varint(i);
    }
    this.inlineStr(s);
  }

  strHeader(len) {
    if (this.fuse && len < 32) this.w.u8(SSTR | len); else { this.w.u8(TAG.STR); this.w.varint(len); }
  }

  inlineStr(s) {
    const w = this.w, len = s.length;
    if (len <= 128) {
      let ascii = true;
      for (let i = 0; i < len; i++) if (s.charCodeAt(i) > 127) { ascii = false; break; }
      if (ascii) {
        this.strHeader(len); w.need(len);
        const b = w.b, p = w.n;
        for (let i = 0; i < len; i++) b[p + i] = s.charCodeAt(i);
        w.n += len;
        return;
      }
    }
    if (!wellFormed(s)) { w.u8(TAG.WSTR); w.varint(len * 2); return w.bytes(utf16Bytes(s)); }
    const u = enc.encode(s); this.strHeader(u.length); w.bytes(u);
  }

  arrHeader(n) {
    if (this.fuse && n < 16) this.w.u8(SARR | n); else { this.w.u8(TAG.ARR); this.w.varint(n); }
  }

  array(a) {
    const n = a.length;
    if (n > 0) {
      const t0 = typeof a[0];
      if (t0 === 'number') {
        let all = true;
        for (let i = 1; i < n; i++) if (typeof a[i] !== 'number') { all = false; break; }
        if (all) return this.numArr(a);
      } else if (this.packed && t0 === 'boolean') { if (this.boolArr(a)) return; }
      else if (this.packed && t0 === 'string') { if (this.enumArr(a)) return; }
      else if (this.columnar && t0 === 'object' && n >= MINROWS) { if (this.cols(a)) return; }
    }
    this.arrHeader(n);
    for (let i = 0; i < n; i++) {
      const x = a[i];
      if (x === undefined && !(i in a)) this.w.u8(TAG.HOLE); else this.write(x);
    }
  }

  numArr(a) {
    const w = this.w, n = a.length;
    let k = 0, ok = true, negz = null;       // negz: posiciones de los -0 (el entero escalado los guarda como 0)
    for (let i = 0; i < n; i++) {
      const x = a[i];
      if (!Number.isFinite(x)) { ok = false; break; }
      if (x === 0 && 1 / x < 0) (negz ||= []).push(i);
      while (k <= 9 && !okAt(x, k)) k++;
      if (k > 9) { ok = false; break; }
    }
    if (ok) {
      if (scratch.length < n) scratch = new Float64Array(Math.max(n, scratch.length * 2));
      const pk = POW[k];
      let s1 = 0, s2 = 0, prev = 0, okD = true;
      for (let i = 0; i < n; i++) {
        const x = a[i], m = Math.round(x * pk);
        if (m / pk !== x || m > MAXP || m < -MAXP) { ok = false; break; }
        scratch[i] = m;
        s1 += vlen(zz(m));
        const d = m - prev;
        if (d > MAXP || d < -MAXP) okD = false; else if (okD) s2 += vlen(zz(d));
        prev = m;
      }
      if (ok) {
        const delta = okD && s2 < s1;
        w.u8(delta ? TAG.ADELTA : TAG.AINT); w.varint(n); w.u8(negz ? k | 0x80 : k);
        prev = 0;
        if (delta) for (let i = 0; i < n; i++) { const m = scratch[i]; w.varint(zz(m - prev)); prev = m; }
        else for (let i = 0; i < n; i++) w.varint(zz(scratch[i]));
        if (negz) { w.varint(negz.length); prev = 0; for (const p of negz) { w.varint(p - prev); prev = p; } }
        return;
      }
    }
    let all32 = true;
    for (let i = 0; i < n; i++) if (Math.fround(a[i]) !== a[i] && a[i] === a[i]) { all32 = false; break; }
    // NaN no es igual a sí mismo: float32 también lo guarda (como NaN), por eso se excluye de la prueba
    if (all32) { w.u8(TAG.AF32); w.varint(n); for (let i = 0; i < n; i++) w.f32(a[i]); }
    else { w.u8(TAG.AF64); w.varint(n); for (let i = 0; i < n; i++) w.f64(a[i]); }
  }

  boolArr(a) {
    const w = this.w, n = a.length;
    for (let i = 0; i < n; i++) if (typeof a[i] !== 'boolean') return false;
    const generic = (this.fuse && n < 16 ? 1 : 1 + vlen(n)) + n, bits = 1 + vlen(n) + ((n + 7) >> 3);
    if (bits >= generic) return false;
    const tmp = new Uint8Array((n + 7) >> 3);
    for (let i = 0; i < n; i++) if (a[i]) tmp[i >> 3] |= 1 << (i & 7);
    w.u8(TAG.ABOOL); w.varint(n); w.bytes(tmp);
    return true;
  }

  enumArr(a) {
    const w = this.w, n = a.length, ids = new Map(), tix = [], idx = this.idx, fuse = this.fuse;
    let generic = fuse && n < 16 ? 1 : 1 + vlen(n);
    for (let i = 0; i < n; i++) {
      const s = a[i];
      if (typeof s !== 'string') return false;
      const ti = idx.get(s);
      if (ti === undefined) return false;
      if (!ids.has(s)) { ids.set(s, tix.length); tix.push(ti); if (tix.length > 256) return false; }
      generic += fuse ? (ti < 32 ? 1 : 1 + vlen(ti)) : 1 + vlen(ti);
    }
    const d = tix.length, bits = d <= 1 ? 0 : 32 - Math.clz32(d - 1);
    let cost = 1 + vlen(n) + vlen(d) + ((n * bits + 7) >> 3);
    for (const t of tix) cost += vlen(t);
    if (cost >= generic) return false;
    w.u8(TAG.AENUM); w.varint(n); w.varint(d);
    for (const t of tix) w.varint(t);
    if (bits > 0) {
      const tmp = new Uint8Array((n * bits + 7) >> 3);
      for (let i = 0; i < n; i++) {
        const v = ids.get(a[i]), bit = i * bits, by = bit >> 3, sh = bit & 7;
        tmp[by] |= (v << sh) & 255;
        if (sh + bits > 8) tmp[by + 1] |= (v >> (8 - sh)) & 255;
      }
      w.bytes(tmp);
    }
    return true;
  }

  // Array de objetos "parecidos" -> una columna por clave. Cada clave puede faltar en algunas filas
  // (queda un bitmap de presencia), siempre que el orden relativo de las claves sea consistente.
  cols(a) {
    const w = this.w, n = a.length, dups = this.dups, f = a[0];
    if (f === null || Object.getPrototypeOf(f) !== OP) return false;
    const base = Object.keys(f), bn = base.length;
    let uniform = true;
    for (let i = 0; i < n; i++) {
      const x = a[i];
      if (x === null || typeof x !== 'object' || Object.getPrototypeOf(x) !== OP) return false;
      if (dups !== null && dups.has(x)) return false;        // una fila compartida no puede perder su identidad
      if (uniform) {
        const ks = Object.keys(x);
        if (ks.length !== bn) uniform = false;
        else for (let j = 0; j < bn; j++) if (ks[j] !== base[j]) { uniform = false; break; }
      }
    }
    let union = base, pres = null, cnt = null;
    if (!uniform) {
      // orden de columnas compatible con el orden de claves de todas las filas (orden topológico)
      const ids = new Map(), names = [], presBy = [], cntBy = [], adj = new Uint8Array(MAXCOLS * MAXCOLS);
      let total = 0;
      for (let i = 0; i < n; i++) {
        const ks = Object.keys(a[i]); let prev = -1;
        for (let j = 0; j < ks.length; j++) {
          const k = ks[j]; let id = ids.get(k);
          if (id === undefined) {
            if (names.length >= MAXCOLS) return false;
            id = names.length; ids.set(k, id); names.push(k); presBy.push(new Uint8Array(n)); cntBy.push(0);
          }
          presBy[id][i] = 1; cntBy[id]++;
          if (prev >= 0) adj[prev * MAXCOLS + id] = 1;
          prev = id;
        }
        total += ks.length;
      }
      const nc = names.length, indeg = new Array(nc).fill(0), done = new Array(nc).fill(false), order = [];
      for (let u = 0; u < nc; u++) for (let v = 0; v < nc; v++) if (adj[u * MAXCOLS + v]) indeg[v]++;
      for (let step = 0; step < nc; step++) {
        let u = 0; while (u < nc && (done[u] || indeg[u] !== 0)) u++;
        if (u === nc) return false;                          // órdenes de claves incompatibles entre filas
        done[u] = true; order.push(u);
        for (let v = 0; v < nc; v++) if (adj[u * MAXCOLS + v]) indeg[v]--;
      }
      union = order.map(u => names[u]); pres = order.map(u => presBy[u]); cnt = order.map(u => cntBy[u]);
      // por fila se ahorran el encabezado y un byte por clave; cada columna opcional cuesta un bitmap de n/8 bytes
      let optCols = 0;
      for (let j = 0; j < nc; j++) if (cnt[j] < n) optCols++;
      if (optCols * ((n + 7) >> 3) + nc >= n + total) return false;
    }
    const c = union.length, opt = new Array(c);
    w.u8(TAG.COLS); w.varint(n); w.varint(c);
    for (let j = 0; j < c; j++) {
      opt[j] = !uniform && cnt[j] < n;
      w.varint(this.idx.get(union[j]) * 2 + (opt[j] ? 1 : 0));
    }
    for (let j = 0; j < c; j++) {
      const key = union[j];
      let vals;
      if (opt[j]) {
        const tmp = new Uint8Array((n + 7) >> 3), p = pres[j];
        vals = [];
        for (let i = 0; i < n; i++) if (p[i]) { tmp[i >> 3] |= 1 << (i & 7); vals.push(a[i][key]); }
        w.bytes(tmp);
      } else {
        vals = new Array(n);
        for (let i = 0; i < n; i++) vals[i] = a[i][key];
      }
      this.array(vals);
    }
    return true;
  }
}

class Decoder {
  constructor(u8, opts) {
    this.u8 = u8;
    this.dv = new DataView(u8.buffer, u8.byteOffset, u8.byteLength);
    this.p = 0;
    this.fastAscii = opts.fastAscii !== false;
    this.tbl = [];
    this.objs = [];            // objetos marcados con OBJDEF, en orden de aparición
    this.defNext = false;
  }

  run() {
    const u8 = this.u8;
    if (u8[this.p++] !== MAGIC) throw new Error('Pack2: no es un archivo Pack2 (byte mágico incorrecto)');
    const nt = this.varint(), tbl = this.tbl = new Array(nt);
    for (let i = 0; i < nt; i++) {
      const h = this.varint(), n = Math.floor(h / 2);
      tbl[i] = h % 2 ? this.wide(n) : this.str(n);
    }
    return this.val();
  }

  varint() {
    const u8 = this.u8;
    let b = u8[this.p++];
    if (b < 128) return b;
    let r = b & 127, m = 128;
    do { b = u8[this.p++]; r += (b & 127) * m; m *= 128; } while (b & 128);
    return r;
  }

  str(n) {
    const u8 = this.u8, p = this.p, e = p + n;
    if (this.fastAscii && n <= 16) {
      let s = '';
      for (let i = p; i < e; i++) {
        const c = u8[i];
        if (c > 127) { this.p = e; return dec.decode(u8.subarray(p, e)); }
        s += String.fromCharCode(c);
      }
      this.p = e; return s;
    }
    this.p = e; return dec.decode(u8.subarray(p, e));
  }

  wide(n) {
    const dv = this.dv, e = this.p + n;
    let s = '', buf = [];
    for (let p = this.p; p < e; p += 2) {
      buf.push(dv.getUint16(p, true));
      if (buf.length === 4096) { s += String.fromCharCode.apply(null, buf); buf.length = 0; }
    }
    if (buf.length) s += String.fromCharCode.apply(null, buf);
    this.p = e; return s;
  }

  reg(o) {
    if (this.defNext) { this.defNext = false; this.objs.push(o); }
    return o;
  }

  readArr(n) {
    const a = this.reg(new Array(n));
    for (let i = 0; i < n; i++) { const v = this.val(); if (v !== HOLE) a[i] = v; }
    return a;
  }

  readObj(n) {
    const o = this.reg({}), tbl = this.tbl;
    for (let i = 0; i < n; i++) {
      const k = tbl[this.varint()], v = this.val();
      if (k === '__proto__') Object.defineProperty(o, k, { value: v, enumerable: true, writable: true, configurable: true });
      else o[k] = v;
    }
    return o;
  }

  val() {
    const u8 = this.u8, t = u8[this.p++];
    if (t >= 0x80) return t & 0x7f;
    if (t >= 0x20) {
      if (t < 0x40) return this.str(t & 31);
      if (t < 0x60) return this.tbl[t & 31];
      if (t < 0x70) return this.readArr(t & 15);
      return this.readObj(t & 15);
    }
    const dv = this.dv;
    switch (t) {
      case TAG.NULL: return null;
      case TAG.FALSE: return false;
      case TAG.TRUE: return true;
      case TAG.UNDEF: return undefined;
      case TAG.HOLE: return HOLE;
      case TAG.UINT: return this.varint();
      case TAG.NINT: return -this.varint();
      case TAG.F32: { const x = dv.getFloat32(this.p, true); this.p += 4; return x; }
      case TAG.F64: { const x = dv.getFloat64(this.p, true); this.p += 8; return x; }
      case TAG.DEC: { const k = u8[this.p++]; return unzz(this.varint()) / POW[k]; }
      case TAG.STR: return this.str(this.varint());
      case TAG.WSTR: return this.wide(this.varint());
      case TAG.REF: return this.tbl[this.varint()];
      case TAG.ARR: return this.readArr(this.varint());
      case TAG.OBJ: return this.readObj(this.varint());
      case TAG.AINT: case TAG.ADELTA: {
        const n = this.varint(), kb = u8[this.p++], d = POW[kb & 0x7f], a = this.reg(new Array(n));
        let prev = 0;
        if (t === TAG.AINT) for (let i = 0; i < n; i++) a[i] = unzz(this.varint()) / d;
        else for (let i = 0; i < n; i++) { prev += unzz(this.varint()); a[i] = prev / d; }
        if (kb & 0x80) { const c = this.varint(); let p = 0; for (let i = 0; i < c; i++) { p += this.varint(); a[p] = -0; } }
        return a;
      }
      case TAG.AF32: { const n = this.varint(), a = this.reg(new Array(n)); for (let i = 0; i < n; i++) { a[i] = dv.getFloat32(this.p, true); this.p += 4; } return a; }
      case TAG.AF64: { const n = this.varint(), a = this.reg(new Array(n)); for (let i = 0; i < n; i++) { a[i] = dv.getFloat64(this.p, true); this.p += 8; } return a; }
      case TAG.ABOOL: {
        const n = this.varint(), a = this.reg(new Array(n)), p = this.p;
        for (let i = 0; i < n; i++) a[i] = ((u8[p + (i >> 3)] >> (i & 7)) & 1) === 1;
        this.p += (n + 7) >> 3; return a;
      }
      case TAG.AENUM: {
        const n = this.varint(), d = this.varint(), ss = new Array(d), a = this.reg(new Array(n));
        for (let j = 0; j < d; j++) ss[j] = this.tbl[this.varint()];
        const bits = d <= 1 ? 0 : 32 - Math.clz32(d - 1), mask = (1 << bits) - 1, p = this.p;
        if (bits === 0) for (let i = 0; i < n; i++) a[i] = ss[0];
        else for (let i = 0; i < n; i++) {
          const bit = i * bits, by = p + (bit >> 3), sh = bit & 7;
          a[i] = ss[((u8[by] | (u8[by + 1] << 8)) >> sh) & mask];
        }
        this.p += (n * bits + 7) >> 3; return a;
      }
      case TAG.COLS: return this.readCols();
      case TAG.BIGINT: {
        const neg = u8[this.p++], n = this.varint();
        let hex = '';
        for (let i = 0; i < n; i++) hex += u8[this.p + i].toString(16).padStart(2, '0');
        this.p += n;
        const m = BigInt('0x' + hex);
        return neg ? -m : m;
      }
      case TAG.DATE: { const d = new Date(dv.getFloat64(this.p, true)); this.p += 8; return this.reg(d); }
      case TAG.MAP: {
        const m = this.reg(new Map()), n = this.varint();
        for (let i = 0; i < n; i++) { const k = this.val(), v = this.val(); m.set(k, v); }
        return m;
      }
      case TAG.SET: {
        const s = this.reg(new Set()), n = this.varint();
        for (let i = 0; i < n; i++) s.add(this.val());
        return s;
      }
      case TAG.TYPED: {
        const kind = u8[this.p++], len = this.varint(), C = TYPED[kind];
        const bytes = u8.slice(this.p, this.p + len);        // copia alineada
        this.p += len;
        return this.reg(new C(bytes.buffer, 0, len / C.BYTES_PER_ELEMENT));
      }
      case TAG.ABUF: {
        const len = this.varint(), b = u8.slice(this.p, this.p + len).buffer;
        this.p += len; return this.reg(b);
      }
      case TAG.REGEXP: { const src = this.val(), flags = this.val(); return this.reg(new RegExp(src, flags)); }
      case TAG.ERROR: {
        const name = this.val(), msg = this.val(), stack = this.val();
        const C = ERRORS[name] || Error, e = new C(msg);
        if (!ERRORS[name]) e.name = name;
        e.stack = stack;
        return this.reg(e);
      }
      case TAG.OBJDEF: this.defNext = true; return this.val();
      case TAG.OBJREF: return this.objs[this.varint()];
      default: throw new Error('Pack2: tag desconocido 0x' + t.toString(16) + ' en el offset ' + (this.p - 1));
    }
  }

  readCols() {
    const n = this.varint(), c = this.varint(), out = this.reg(new Array(n)), u8 = this.u8, tbl = this.tbl;
    const keys = new Array(c), opt = new Array(c);
    let anyOpt = false;
    for (let j = 0; j < c; j++) {
      const h = this.varint();
      keys[j] = tbl[Math.floor(h / 2)]; opt[j] = h % 2 === 1;
      if (opt[j]) anyOpt = true;
    }
    const cols = new Array(c), maps = new Array(c), nb = (n + 7) >> 3;
    for (let j = 0; j < c; j++) {
      if (opt[j]) { maps[j] = u8.subarray(this.p, this.p + nb); this.p += nb; }
      cols[j] = this.val();
    }
    const hasProto = keys.includes('__proto__');
    const put = (o, k, v) => {
      if (hasProto && k === '__proto__') Object.defineProperty(o, k, { value: v, enumerable: true, writable: true, configurable: true });
      else o[k] = v;
    };
    if (!anyOpt) {
      for (let i = 0; i < n; i++) {
        const o = {};
        for (let j = 0; j < c; j++) put(o, keys[j], cols[j][i]);
        out[i] = o;
      }
    } else {
      const cur = new Array(c).fill(0);
      for (let i = 0; i < n; i++) {
        const o = {};
        for (let j = 0; j < c; j++) {
          if (opt[j] && !((maps[j][i >> 3] >> (i & 7)) & 1)) continue;
          put(o, keys[j], cols[j][cur[j]++]);
        }
        out[i] = o;
      }
    }
    return out;
  }
}

export default class Pack2 {
  static VERSION = '2.1.0';
  static FORMAT = 3;
  static MAGIC = MAGIC;
  static TAG = TAG;
  /** Opciones por defecto. `fuse`, `columnar`, `packed` y `refs` se pueden apagar para medir qué aporta cada una. */
  static defaults = Object.freeze({ fuse: true, columnar: true, packed: true, refs: true, fastAscii: true });
  /** Estadísticas de la última llamada a encode: { tableBytes, tableEntries, valueBytes, sharedObjects }. */
  static stats = null;

  /**
   * Codifica un valor a bytes.
   * @param {*} value
   * @param {{fuse?:boolean, columnar?:boolean, packed?:boolean, refs?:boolean}} [options]
   *   refs:false desactiva la detección de referencias compartidas/circulares (más rápido; un ciclo lanza TypeError).
   * @returns {Uint8Array}
   */
  static encode(value, options) {
    const e = new Encoder(options ? { ...Pack2.defaults, ...options } : Pack2.defaults);
    let out;
    try { out = e.run(value); }
    catch (err) {
      if (err instanceof RangeError && /call stack/i.test(err.message)) {
        throw new TypeError('Pack2: estructura demasiado profunda o con referencia circular (probá con refs:true)');
      }
      throw err;
    }
    Pack2.stats = { tableBytes: e.tableEnd, tableEntries: e.tbl.length, valueBytes: out.length - e.tableEnd, sharedObjects: e.dups ? e.dups.size : 0 };
    return out;
  }

  /**
   * Decodifica bytes producidos por encode.
   * @param {Uint8Array|ArrayBuffer} bytes
   * @param {{fastAscii?:boolean}} [options]
   */
  static decode(bytes, options) {
    if (bytes instanceof ArrayBuffer) bytes = new Uint8Array(bytes);
    return new Decoder(bytes, options ? { ...Pack2.defaults, ...options } : Pack2.defaults).run();
  }

  /** Comprime bytes con CompressionStream ('gzip', 'deflate' o 'deflate-raw'). */
  static async compress(bytes, format = 'gzip') {
    const stream = new Blob([bytes]).stream().pipeThrough(new CompressionStream(format));
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }

  static async decompress(bytes, format = 'gzip') {
    const stream = new Blob([bytes]).stream().pipeThrough(new DecompressionStream(format));
    return new Uint8Array(await new Response(stream).arrayBuffer());
  }

  /** encode + compress. `options.format` elige el algoritmo (por defecto 'gzip'). */
  static async encodeCompressed(value, options) {
    return Pack2.compress(Pack2.encode(value, options), options?.format);
  }

  static async decodeCompressed(bytes, options) {
    return Pack2.decode(await Pack2.decompress(bytes, options?.format), options);
  }
}

export { Pack2 };
