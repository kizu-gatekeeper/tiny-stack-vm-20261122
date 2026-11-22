import { mkdirSync, readFileSync, readdirSync, writeFileSync } from "node:fs";

// Tiny stack VM, ISA v1. Values are int32 and wrap; data stack <= 256,
// call stack <= 64 return addresses, memory 256 words, at most
// 1,000,000 steps and 65,536 output bytes per program.
function run(p, inp) {
  const S = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const O = Buffer.alloc(65536);
  let sp = 0, cp = 0, pc = 0, ip = 0, st = 0, ol = 0, ex = 0;
  const n = p.length;
  outer: while (true) {
    if (st >= 1000000) { ex = 10; break; }
    if (pc < 0 || pc >= n) { ex = 9; break; }
    const op = p[pc];
    st++;
    switch (op) {
      case 0x00: ex = 0; break outer;
      case 0x01: // PUSH8, signed 8-bit
        if (pc + 2 > n) { ex = 9; break outer; }
        if (sp > 255) { ex = 3; break outer; }
        S[sp++] = (p[pc + 1] << 24) >> 24;
        pc += 2;
        break;
      case 0x02: // PUSH32, signed 32-bit little-endian
        if (pc + 5 > n) { ex = 9; break outer; }
        if (sp > 255) { ex = 3; break outer; }
        S[sp++] = p[pc + 1] | (p[pc + 2] << 8) | (p[pc + 3] << 16) | (p[pc + 4] << 24);
        pc += 5;
        break;
      case 0x03: // POP
        if (sp < 1) { ex = 2; break outer; }
        sp--;
        pc++;
        break;
      case 0x04: // DUP
        if (sp < 1) { ex = 2; break outer; }
        if (sp > 255) { ex = 3; break outer; }
        S[sp] = S[sp - 1];
        sp++;
        pc++;
        break;
      case 0x05: // SWAP
        if (sp < 2) { ex = 2; break outer; }
        { const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; }
        pc++;
        break;
      case 0x06: // OVER
        if (sp < 2) { ex = 2; break outer; }
        if (sp > 255) { ex = 3; break outer; }
        S[sp] = S[sp - 2];
        sp++;
        pc++;
        break;
      case 0x07: // ROT (a b c -- b c a)
        if (sp < 3) { ex = 2; break outer; }
        { const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; }
        pc++;
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: { // binary ops (a b -- r)
        if (sp < 2) { ex = 2; break outer; }
        const b = S[--sp], a = S[sp - 1];
        let r = 0;
        if (op === 0x10) r = (a + b) | 0; // ADD wraps
        else if (op === 0x11) r = (a - b) | 0; // SUB wraps
        else if (op === 0x12) r = Math.imul(a, b); // MUL low 32 bits
        else if (op === 0x13) { if (!b) { ex = 4; break outer; } r = (a / b) | 0; } // DIV truncates, INT_MIN/-1 wraps
        else if (op === 0x14) { if (!b) { ex = 4; break outer; } r = (a % b) | 0; } // MOD sign of a, x%-1 is 0
        else if (op === 0x15) { if (!b) { ex = 4; break outer; } r = Math.floor((a >>> 0) / (b >>> 0)) | 0; } // DIVU
        else if (op === 0x16) { if (!b) { ex = 4; break outer; } r = ((a >>> 0) % (b >>> 0)) | 0; } // MODU
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31); // SHL
        else if (op === 0x1d) r = a >> (b & 31); // SHR arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // SHRU logical
        else if (op === 0x20) r = a === b ? 1 : 0; // EQ
        else if (op === 0x21) r = a < b ? 1 : 0; // LT signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // LTU unsigned
        S[sp - 1] = r;
        pc++;
        break;
      }
      case 0x17: // NEG wraps
        if (sp < 1) { ex = 2; break outer; }
        S[sp - 1] = (-S[sp - 1]) | 0;
        pc++;
        break;
      case 0x1b: // NOT
        if (sp < 1) { ex = 2; break outer; }
        S[sp - 1] = ~S[sp - 1];
        pc++;
        break;
      case 0x30: // JMP, signed 16-bit offset from next instruction
        if (pc + 3 > n) { ex = 9; break outer; }
        pc = pc + 3 + (((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16);
        break;
      case 0x31: case 0x32: { // JZ / JNZ
        if (pc + 3 > n) { ex = 9; break outer; }
        if (sp < 1) { ex = 2; break outer; }
        const v = S[--sp];
        const off = ((p[pc + 1] | (p[pc + 2] << 8)) << 16) >> 16;
        pc = (op === 0x31 ? v === 0 : v !== 0) ? pc + 3 + off : pc + 3;
        break;
      }
      case 0x33: // CALL, unsigned 16-bit absolute target
        if (pc + 3 > n) { ex = 9; break outer; }
        if (cp > 63) { ex = 7; break outer; }
        C[cp++] = pc + 3;
        pc = p[pc + 1] | (p[pc + 2] << 8);
        break;
      case 0x34: // RET
        if (cp < 1) { ex = 8; break outer; }
        pc = C[--cp];
        break;
      case 0x40: // LOAD
        if (sp < 1) { ex = 2; break outer; }
        { const a = S[sp - 1]; if (a < 0 || a > 255) { ex = 6; break outer; } S[sp - 1] = M[a]; }
        pc++;
        break;
      case 0x41: // STORE (v addr --)
        if (sp < 2) { ex = 2; break outer; }
        { const a = S[--sp], v = S[--sp]; if (a < 0 || a > 255) { ex = 6; break outer; } M[a] = v; }
        pc++;
        break;
      case 0x50: // PRINT decimal ASCII, no newline
        if (sp < 1) { ex = 2; break outer; }
        { const t = String(S[--sp]); if (ol + t.length > 65536) { ex = 11; break outer; } ol += O.write(t, ol); }
        pc++;
        break;
      case 0x51: // PUTC one byte
        if (sp < 1) { ex = 2; break outer; }
        if (ol + 1 > 65536) { ex = 11; break outer; }
        O[ol++] = S[--sp] & 255;
        pc++;
        break;
      case 0x52: // IN next input byte, -1 when used up
        if (sp > 255) { ex = 3; break outer; }
        S[sp++] = ip < inp.length ? inp[ip++] : -1;
        pc++;
        break;
      case 0x53: // EXIT with code v AND 255
        if (sp < 1) { ex = 2; break outer; }
        ex = S[--sp] & 255;
        break outer;
      default: ex = 5; break outer; // unknown opcode
    }
  }
  return [O.subarray(0, ol), ex];
}

const INDIR = process.env.MAKEFUN_INPUT_DIR ?? "/input";
const OUTDIR = process.env.MAKEFUN_OUTPUT_DIR ?? "/output";
for (const id of readdirSync(INDIR).sort()) {
  let prog, inp;
  try {
    prog = readFileSync(INDIR + "/" + id + "/program.bin");
    inp = readFileSync(INDIR + "/" + id + "/input.bin");
  } catch { continue; }
  const [out, ex] = run(prog, inp);
  mkdirSync(OUTDIR + "/" + id, { recursive: true });
  writeFileSync(OUTDIR + "/" + id + "/stdout.bin", out);
  writeFileSync(OUTDIR + "/" + id + "/exit.txt", String(ex));
}
