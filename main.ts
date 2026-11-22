// Tiny stack VM entry: runs every bytecode program in the input folder
// against its input bytes and writes stdout + exit code for each one.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Per-opcode facts: byte -> [immediate size, values popped, values pushed].
const INFO = {
  0: [0, 0, 0], 1: [1, 0, 1], 2: [4, 0, 1], 3: [0, 1, 0], 4: [0, 1, 2],
  5: [0, 2, 2], 6: [0, 2, 3], 7: [0, 3, 3],
  16: [0, 2, 1], 17: [0, 2, 1], 18: [0, 2, 1], 19: [0, 2, 1], 20: [0, 2, 1],
  21: [0, 2, 1], 22: [0, 2, 1], 23: [0, 1, 1], 24: [0, 2, 1], 25: [0, 2, 1],
  26: [0, 2, 1], 27: [0, 1, 1], 28: [0, 2, 1], 29: [0, 2, 1], 30: [0, 2, 1],
  32: [0, 2, 1], 33: [0, 2, 1], 34: [0, 2, 1],
  48: [2, 0, 0], 49: [2, 1, 0], 50: [2, 1, 0], 51: [2, 0, 0], 52: [0, 0, 0],
  64: [0, 1, 1], 65: [0, 2, 0],
  80: [0, 1, 0], 81: [0, 1, 0], 82: [0, 0, 1], 83: [0, 1, 0],
};
const BIN = new Set([16, 17, 18, 19, 20, 21, 22, 24, 25, 26, 28, 29, 30, 32, 33, 34]);
const enc = new TextEncoder();

// Two-operand arithmetic for the BIN set; a zero divisor traps 4.
function binCalc(op, a, b) {
  if (op === 16) return (a + b) | 0;
  if (op === 17) return (a - b) | 0;
  if (op === 18) return Math.imul(a, b);
  if (op === 19) { if (b === 0) throw 4; return a === -2147483648 && b === -1 ? a : (a / b) | 0; }
  if (op === 20) { if (b === 0) throw 4; return b === -1 ? 0 : a % b | 0; }
  if (op === 21) { if (b === 0) throw 4; return Math.floor((a >>> 0) / (b >>> 0)) | 0; }
  if (op === 22) { if (b === 0) throw 4; return (a >>> 0) % (b >>> 0) | 0; }
  if (op === 24) return a & b;
  if (op === 25) return a | b;
  if (op === 26) return a ^ b;
  if (op === 28) return a << (b & 31);
  if (op === 29) return a >> (b & 31);
  if (op === 30) return (a >>> (b & 31)) | 0;
  if (op === 32) return a === b ? 1 : 0;
  if (op === 33) return a < b ? 1 : 0;
  return (a >>> 0) < (b >>> 0) ? 1 : 0;
}

function runProgram(prog, input) {
  const st = new Int32Array(256);
  const rt = new Int32Array(64);
  const mem = new Int32Array(256);
  const buf = new Uint8Array(65536);
  let sp = 0, rp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const finish = (code) => ({ bytes: buf.slice(0, olen), code });
  try {
    for (;;) {
      if (steps === 1000000) throw 10;
      if (pc < 0 || pc >= prog.length) throw 9;
      const op = prog[pc];
      const info = INFO[op];
      if (info === undefined) throw 5;
      const [imm, pops, pushes] = info;
      if (pc + imm >= prog.length) throw 9;
      steps++;
      const nx = pc + 1 + imm;
      if (sp < pops) throw 2;
      if (sp - pops + pushes > 256) throw 3;
      pc = nx;
      if (op === 0) return finish(0);
      else if (op === 1) st[sp++] = (prog[nx - 1] << 24) >> 24;
      else if (op === 2) st[sp++] = prog[nx - 4] | (prog[nx - 3] << 8) | (prog[nx - 2] << 16) | (prog[nx - 1] << 24);
      else if (op === 3) sp--;
      else if (op === 4) { st[sp] = st[sp - 1]; sp++; }
      else if (op === 5) { const t = st[sp - 1]; st[sp - 1] = st[sp - 2]; st[sp - 2] = t; }
      else if (op === 6) { st[sp] = st[sp - 2]; sp++; }
      else if (op === 7) { const a = st[sp - 3]; st[sp - 3] = st[sp - 2]; st[sp - 2] = st[sp - 1]; st[sp - 1] = a; }
      else if (op === 23) st[sp - 1] = -st[sp - 1] | 0;
      else if (op === 27) st[sp - 1] = ~st[sp - 1];
      else if (BIN.has(op)) { const b = st[sp - 1], a = st[sp - 2]; const r = binCalc(op, a, b); sp -= 2; st[sp++] = r; }
      else if (op === 48 || op === 49 || op === 50) {
        const rel = ((prog[nx - 2] | (prog[nx - 1] << 8)) << 16) >> 16;
        let go = true;
        if (op !== 48) { const v = st[--sp]; go = op === 49 ? v === 0 : v !== 0; }
        if (go) pc = nx + rel;
      }
      else if (op === 51) { if (rp === 64) throw 7; rt[rp++] = nx; pc = prog[nx - 2] | (prog[nx - 1] << 8); }
      else if (op === 52) { if (rp === 0) throw 8; pc = rt[--rp]; }
      else if (op === 64) { const a = st[sp - 1]; if (a < 0 || a > 255) throw 6; st[sp - 1] = mem[a]; }
      else if (op === 65) { const a = st[sp - 1]; if (a < 0 || a > 255) throw 6; sp -= 2; mem[a] = st[sp]; }
      else if (op === 80) { const bs = enc.encode(String(st[sp - 1])); if (olen + bs.length > 65536) throw 11; sp--; buf.set(bs, olen); olen += bs.length; }
      else if (op === 81) { if (olen + 1 > 65536) throw 11; buf[olen++] = st[--sp] & 255; }
      else if (op === 82) st[sp++] = ip < input.length ? input[ip++] : -1;
      else if (op === 83) return finish(st[--sp] & 255);
    }
  } catch (e) {
    return finish(e);
  }
}

const inDir = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const outDir = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(inDir).sort()) {
  const prog = new Uint8Array(readFileSync(join(inDir, id, 'program.bin')));
  const input = new Uint8Array(readFileSync(join(inDir, id, 'input.bin')));
  const r = runProgram(prog, input);
  mkdirSync(join(outDir, id), { recursive: true });
  writeFileSync(join(outDir, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(outDir, id, 'exit.txt'), r.code + '\n');
}
