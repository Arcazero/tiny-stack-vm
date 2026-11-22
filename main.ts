// Tiny stack VM: make.fun tiny stack ISA v1. Node 22, stdlib only.
import { existsSync, mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// Opcode table: one "imm pops pushes" triple per byte 0x00..0x53; "999" = invalid.
const T = '000101401010012022023033' +
  '999999999999999999999999' +
  '021021021021021021021011021021021011021021021999021021021' +
  '999999999999999999999999999999999999999' +
  '200210210200000' +
  '999999999999999999999999999999999' +
  '011020' +
  '999999999999999999999999999999999999999999' +
  '010010001010';

const STEP_LIMIT = 1_000_000;
const OUTPUT_MAX = 65_536;
const STACK_MAX = 256;
const CALLS_MAX = 64;
const MEMORY_WORDS = 256;

function run(program: Uint8Array, input: Uint8Array): [Uint8Array, number] {
  const n = program.length;
  const stack = new Int32Array(STACK_MAX);
  let sp = 0;
  const calls = new Int32Array(CALLS_MAX);
  let csp = 0;
  const memory = new Int32Array(MEMORY_WORDS);
  const out = new Uint8Array(OUTPUT_MAX);
  let olen = 0;
  let inPos = 0;
  let pc = 0;
  let steps = 0;

  for (;;) {
    if (steps === STEP_LIMIT) return [out.slice(0, olen), 10];
    if (pc < 0 || pc >= n) return [out.slice(0, olen), 9];
    const op = program[pc];
    const q = op * 3;
    if (op > 0x53 || T[q] === '9') return [out.slice(0, olen), 5];
    const imm = +T[q], pops = +T[q + 1], pushes = +T[q + 2];
    if (pc + imm >= n) return [out.slice(0, olen), 9];
    steps++;
    const next = pc + 1 + imm;
    if (sp < pops) return [out.slice(0, olen), 2];
    if (sp - pops + pushes > STACK_MAX) return [out.slice(0, olen), 3];
    pc = next;

    switch (op) {
      case 0x00:
        return [out.slice(0, olen), 0];
      case 0x01:
        stack[sp++] = (program[next - 1] << 24) >> 24;
        break;
      case 0x02:
        stack[sp++] =
          program[next - 4] |
          (program[next - 3] << 8) |
          (program[next - 2] << 16) |
          (program[next - 1] << 24);
        break;
      case 0x03:
        sp--;
        break;
      case 0x04:
        stack[sp] = stack[sp - 1];
        sp++;
        break;
      case 0x05: {
        const t = stack[sp - 1];
        stack[sp - 1] = stack[sp - 2];
        stack[sp - 2] = t;
        break;
      }
      case 0x06:
        stack[sp] = stack[sp - 2];
        sp++;
        break;
      case 0x07: {
        const a = stack[sp - 3];
        stack[sp - 3] = stack[sp - 2];
        stack[sp - 2] = stack[sp - 1];
        stack[sp - 1] = a;
        break;
      }
      case 0x17:
        stack[sp - 1] = (-stack[sp - 1]) | 0;
        break;
      case 0x1b:
        stack[sp - 1] = ~stack[sp - 1];
        break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15:
      case 0x16: case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d:
      case 0x1e: case 0x20: case 0x21: case 0x22: {
        const b = stack[sp - 1], a = stack[sp - 2];
        let r: number;
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13:
            if (b === 0) return [out.slice(0, olen), 4];
            r = a === -2147483648 && b === -1 ? a : (a / b) | 0;
            break;
          case 0x14:
            if (b === 0) return [out.slice(0, olen), 4];
            r = b === -1 ? 0 : (a % b) | 0;
            break;
          case 0x15:
            if (b === 0) return [out.slice(0, olen), 4];
            r = Math.floor((a >>> 0) / (b >>> 0)) | 0;
            break;
          case 0x16:
            if (b === 0) return [out.slice(0, olen), 4];
            r = ((a >>> 0) % (b >>> 0)) | 0;
            break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          default: r = (a >>> 0) < (b >>> 0) ? 1 : 0;
        }
        sp -= 2;
        stack[sp++] = r;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((program[next - 2] | (program[next - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          const v = stack[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        if (take) pc = next + rel;
        break;
      }
      case 0x33:
        if (csp === CALLS_MAX) return [out.slice(0, olen), 7];
        calls[csp++] = next;
        pc = program[next - 2] | (program[next - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return [out.slice(0, olen), 8];
        pc = calls[--csp];
        break;
      case 0x40: {
        const addr = stack[sp - 1];
        if (addr < 0 || addr >= MEMORY_WORDS) return [out.slice(0, olen), 6];
        stack[sp - 1] = memory[addr];
        break;
      }
      case 0x41: {
        const addr = stack[sp - 1];
        const v = stack[sp - 2];
        if (addr < 0 || addr >= MEMORY_WORDS) return [out.slice(0, olen), 6];
        sp -= 2;
        memory[addr] = v;
        break;
      }
      case 0x50: {
        const bytes = new TextEncoder().encode(String(stack[sp - 1]));
        if (olen + bytes.length > OUTPUT_MAX) return [out.slice(0, olen), 11];
        sp--;
        out.set(bytes, olen);
        olen += bytes.length;
        break;
      }
      case 0x51:
        if (olen + 1 > OUTPUT_MAX) return [out.slice(0, olen), 11];
        out[olen++] = stack[--sp] & 255;
        break;
      case 0x52:
        stack[sp++] = inPos < input.length ? input[inPos++] : -1;
        break;
      default:
        return [out.slice(0, olen), stack[--sp] & 255];
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input', O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const d = join(I, id), p = join(d, 'program.bin');
  if (!existsSync(p)) continue;
  const q = join(d, 'input.bin');
  const [stdout, exit] = run(readFileSync(p), existsSync(q) ? readFileSync(q) : Buffer.alloc(0));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), stdout);
  writeFileSync(join(O, id, 'exit.txt'), exit + '\n');
}
