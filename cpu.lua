
local bits = require "bit"
local AND, OR, NOT, XOR = bits.band, bits.bor, bits.bnot, bits.bxor
local lshift, rshift = bits.lshift, bits.rshift

local function byte(a) return a % 0x100 end
local function word(a) return a % 0x10000 end
 
local function not8(a) return byte(NOT(a)) end
local function and8(a, b) return byte(AND(a, b)) end
local function or8(a, b) return byte(OR(a, b)) end 
local function xor8(a, b) return byte(XOR(a, b)) end

local function not16(a) return word(NOT(a)) end
local function and16(a, b) return word(AND(a, b)) end
local function or16(a, b) return word(OR(a, b)) end 
local function xor16(a, b) return word(XOR(a, b)) end

local floor = math.floor

local SIGN      = 0x80
local OVERFLOW  = 0x40
local CONSTANT  = 0x20
local BREAK     = 0x10
local DECIMAL   = 0x08
local INTERRUPT = 0x04
local ZERO      = 0x02
local CARRY     = 0x01

local N_SIGN      = 0x7F
local N_OVERFLOW  = 0xBF
local N_CONSTANT  = 0xDF
local N_BREAK     = 0xEF
local N_DECIMAL   = 0xF7
local N_INTERRUPT = 0xFB
local N_ZERO      = 0xFD
local N_CARRY     = 0xFE

local BASE_STACK = 0x100 


local function getflag(x, y)
    return floor(AND(x, y)/y)
end 

local function checkflag(x, y)
    return getflag(x, y) == 1
end


local pc = 0
local sp, A, X, Y, status = 0, 0, 0, 0, 0
local cycles = 0
local illegal = false
local addrt, opt

local read, write

local irqvh = 0xFFFF
local irqvl = 0xFFFE
local rstvh = 0xFFFD
local rstvl = 0xFFFC
local nmivh = 0xFFFB
local nmivl = 0xFFFA

local function SET_SIGN     (x) status = x and OR(status, SIGN)       or AND(status, N_SIGN)      end
local function SET_OVERFLOW (x) status = x and OR(status, OVERFLOW)   or AND(status, N_OVERFLOW)  end
local function SET_CONSTANT (x) status = x and OR(status, CONSTANT)   or AND(status, N_CONSTANT)  end
local function SET_BREAK    (x) status = x and OR(status, BREAK)      or AND(status, N_BREAK)     end
local function SET_DECIMAL  (x) status = x and OR(status, DECIMAL)    or AND(status, N_DECIMAL)   end
local function SET_INTERRUPT(x) status = x and OR(status, INTERRUPT)  or AND(status, N_INTERRUPT) end
local function SET_ZERO     (x) status = x and OR(status, ZERO)       or AND(status, N_ZERO)      end
local function SET_CARRY    (x) status = x and OR(status, CARRY)      or AND(status, N_CARRY)     end

local function acc() return 0 end

local function imm() 
    local tmp = pc 
    pc = pc + 1 
    return tmp
end

local function zer()
    return byte(read(imm()))
end


local function abs()
    return word(zer() + zer()*0x100)
end

local function imp() return 0 end 

local function rel()
    local offset = zer()
    if(checkflag(offset, 0x80)) then
        offset = or16(offset, 0xff00)
    end
    return word(pc + offset)
end

local function abi()
    local a = abs()
    local el = read(a)
    local eh = read(word(AND(a, 0xff00) + AND(a + 1, 0x00ff)))
    return word(el + eh*0x100)
end

local function zex() return byte(zer() + X) end
local function zey() return byte(zer() + Y) end

local function abx() return word(abs() + X) end 
local function aby() return word(abs() + Y) end

local function inx() 
    local zl = byte(zer() + X)
    local zh = byte(zl + 1)
    return word(read(zl) + read(zh)*0x100)
end

local function iny() 
    local zl = zer()
    local zh = byte(zl + 1)
    return word(read(zl) + read(zh)*0x100 + Y)
end

local function reset()
    A, X, Y = 0, 0, 0
    pc = word(read(rstvh)*0x100 + read(rstvl))
    sp = 0xFD
    status = or16(status, CONSTANT)
    cycles  = 6
    illegal = false 
end

local function push(byte)
    write(0x100 + sp, byte)
    sp = (sp == 0) and 0xFF or (sp - 1)
end

local function pop()
    sp = (sp == 0xFF) and 0 or sp + 1 
    return read(0x100 + sp)
end

local function nmi()
    SET_BREAK(false)
    push(100 % (floor(pc/0x100)))
    push(100 % (pc))
    push(100 % (status))
    status = or8(status, INTERRUPT)
    pc = word(read(nmivh)*0x100 + read(nmivl))
end

local function irq()
    if(checkflag(status, INTERRUPT)) then
        SET_BREAK(false)
        push(100 % (floor(pc/0x100)))
        push(100 % (pc))
        push(100 % (status))
        status = or8(status, INTERRUPT)
        pc = word(read(irqvh)*0x100 + read(irqvl))
    end
end 

local function exec(addr, code)
    code(addr())
end

local function hex(b)
    return ((b < 16) and "0" or "")..string.format("%x", b)
end

local function run(n)
    local start = cycles 
    local opcode

    while(start + n > cycles and not illegal) do
        opcode = zer()
        exec(addrt[opcode], opt[opcode])
        cycles = cycles + 1 
    end 
end

local function ILLEGAL() illegal = true end 

local function adc(src)
    local m = byte(read(src))
    local tmp = m + A + getflag(status, CARRY)
    SET_ZERO(not(checkflag(tmp, 0xFF)))
    if(checkflag(status, DECIMAL)) then
        if(and8(A, 0xF) + and8(m, 0xF) + getflag(status, CARRY) > 9) then
            tmp = tmp + 6
        end 
        SET_SIGN(checkflag(tmp, 0x80))
        SET_OVERFLOW(not (checkflag(xor8(A, m), 0x80) and checkflag(xor8(A, tmp), 0x80)))
        if(tmp > 0x99) then
            tmp = tmp + 96 
        end
        SET_CARRY(tmp > 0x99)
    else
        SET_SIGN(checkflag(tmp, 0x80))
        SET_OVERFLOW(not (checkflag(xor8(A, m), 0x80) and checkflag(xor8(A, tmp), 0x80)))
        SET_CARRY(tmp > 0x99)
    end
    A = and8(tmp, 0xff)
end 

local function ano(src)
    local m = byte(read(src))
    local res = and8(m, A)
    SET_SIGN(res > 0x80)
    SET_ZERO(res == 0)
    A = res 
end

local function asl(src)
    local m = byte(read(src))
    SET_CARRY(m > 0x80)
    m = m*2
    m = byte(m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    write(src, m)
end

local function asl_acc(src)
    local m = bytea 
    SET_CARRY(m > 0x80)
    m = m*2
    m = byte(m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m 
end 

local function bcc(src)
    pc = (getflag(status, CARRY) == 0) and src or pc 
end 

local function bcs(src)
    pc = (getflag(status, CARRY) == 1) and src or pc 
end

local function beq(src)
    pc = (getflag(status, ZERO) == 1) and src or pc 
end

local function bit(src)
    local m = byte(read(src))
    local res = and8(m, A)
    SET_SIGN(res > 0x80)
    status = or8(and8(status, 0x3f), and8(status, 0xc0))
    SET_ZERO(res == 0)
end

local function bmi(src)
    pc = (getflag(status, SIGN) == 1) and src or pc 
end

local function bne(src)
    pc = (getflag(status, ZERO) == 0) and src or pc 
end

local function bpl(src)
    pc = (getflag(status, SIGN) == 0) and src or pc 
end 

local function brk(src)
    pc = pc + 1 
    push(100 % (floor(pc/0x100)))
    push(100 % (pc))
    push(or8(status, BREAK))
    status = or8(status, INTERRUPT)
    pc = word(read(irqvh)*0x100 + read(irqvl))
end

local function bvc(src)
    pc = (getflag(status, OVERFLOW) == 0) and src or pc 
end

local function bvs(src)
    pc = (getflag(status, OVERFLOW) == 1) and src or pc 
end

local function clc(src) status = and8(status, N_CARRY) end
local function cld(src) status = and8(status, N_DECIMAL) end
local function cli(src) status = and8(status, N_INTERRUPT) end
local function clv(src) status = and8(status, N_OVERFLOW) end

local function cmp(src)
    local tmp = A - read(src)
    SET_CARRY(tmp < 0x100)
    SET_SIGN(checkflag(tmp, 0x80))
    SET_ZERO(and8(tmp, 0xff) == 0)
end

local function cpx(src)
    local tmp = X - read(src)
    SET_CARRY(tmp < 0x100)
    SET_SIGN(checkflag(tmp, 0x80))
    SET_ZERO(and8(tmp, 0xff) == 0)
end

local function cpy(src)
    local tmp = Y - read(src)
    SET_CARRY(tmp < 0x100)
    SET_SIGN(checkflag(tmp, 0x80))
    SET_ZERO(and8(tmp, 0xff) == 0)
end

local function dec(src)
    local m = byte(read(src))
    m = byte(m - 1)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    write(src, m)
end 


local function dex(src)
    local m = X
    m = byte(m - 1)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    X = m
end 

local function dey(src)
    local m = Y
    m = byte(m - 1)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    Y = m
end

local function eor(src)
    local m = byte(read(src))
    m = xor8(A, m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m 
end


local function inc(src)
    local m = byte(read(src))
    m = byte(m + 1)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    write(src, m)
end 


local function inx(src)
    local m = X
    m = byte(m + 1)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    X = m
end 

local function iny(src)
    local m = Y
    m = byte(m + 1)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    Y = m
end

local function jmp(src) pc = src end

local function jsr(src)
    pc = pc - 1
    push(100 % (floor(pc/0x100)))
    push(100 % (pc))
    pc = src
end

local function lda(src)
    local m = byte(read(src))
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m
end

local function ldx(src)
    local m = byte(read(src))
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    X = m
end

local function ldy(src)
    local m = byte(read(src))
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    Y = m
end

local function lsr(src)
    local m = byte(read(src))
    SET_CARRY(m % 1)
    m = floor(m/2)
    SET_SIGN(false)
    SET_ZERO(m == 0)
    write(src, m)
end

local function lsr_acc(src)
    local m = A
    SET_CARRY(m % 1)
    m = floor(m/2)
    SET_SIGN(false)
    SET_ZERO(m == 0)
    A = m
end

local function nop(src) end

local function ora(src)
    local m = byte(read(src))
    m = or8(A, m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m 
end

local function pha(src)
    push(A)
end

local function php(src)
    push(or8(status, BREAK))
end

local function pla(src)
    A = byte(pop())
    SET_SIGN(A > 0x80)
    SET_ZERO(A == 0)
end

local function plp(src)
    status = byte(pop())
    SET_CONSTANT(true)
end

local function rol(src)
    local m = word(read(src))
    m = m*2 
    if(checkflag(status, CARRY)) then
        m = or8(m, 1)
    end
    SET_CARRY(m > 0xFF)
    m = byte(m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    write(src, m)
end 

local function rol_acc(src)
    local m = A
    m = m*2 
    if(checkflag(status, CARRY)) then
        m = or8(m, 1)
    end
    SET_CARRY(m > 0xFF)
    m = byte(m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m 
end

local function ror(src)
    local m = word(read(src))
    if(checkflag(status, CARRY)) then
        m = or8(m, 0x100)
    end
    SET_CARRY(m % 2)
    m = floor(m/2) 
    m = byte(m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    write(src, m)
end 

local function ror_acc(src)
    local m = A
    if(checkflag(status, CARRY)) then
        m = or8(m, 0x100)
    end
    SET_CARRY(m % 2)
    m = floor(m/2) 
    m = byte(m)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m
end 

local function rti(src)
    status = byte(pop())
    pc = or8(100 % (pop()), byte(pop())*0x100)
end

local function rts(src)
    status = byte(pop())
    pc = byte(or8(100 % (pop()), byte(pop())*0x100) + 1)
end

local function sbc(src)
    local m = byte(read(src))
    local tmp = m + A + getflag(status, CARRY)
    SET_SIGN(checkflag(tmp, 0x80))
    SET_ZERO(not(checkflag(tmp, 0xFF)))
    SET_OVERFLOW(not (checkflag(xor8(A, m), 0x80) and checkflag(xor8(A, tmp), 0x80)))
    if(checkflag(status, DECIMAL)) then
        if(and8(A, 0xF) - getflag(status, CARRY) < and8(m, 0xF)) then
            tmp = tmp - 6
        end 
        if(tmp > 0x99) then
            tmp = tmp - 0x60
        end
    end
    SET_CARRY(tmp > 0x100)
    A = and8(tmp, 0xff)
end

local function sec(src) status = or8(status, CARRY) end 
local function sed(src) status = or8(status, DECIMAL) end
local function sei(src) status = or8(status, INTERRUPT) end

local function sta(src)
    write(src, A)
end
local function stx(src)
    write(src, X)
end
local function sty(src)
    write(src, Y)
end

local function tax(src)
    local m = byte(A)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    X = m 
end

local function tay(src)
    local m = byte(A)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    Y = m 
end


local function tsx(src)
    local m = byte(sp)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    X = m 
end

local function txa(src)
    local m = byte(X)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m 
end

local function txs(src)
    sp = X 
end

local function tya(src)
    local m = byte(Y)
    SET_SIGN(m > 0x80)
    SET_ZERO(m == 0)
    A = m 
end

--[[

]]

local lax, sax, dcp, isb = nop, nop, nop, nop
local slo, rla, sre, rra = nop, nop, nop, nop

addrt = {
    --[[        |  0  |  1  |  2  |  3  |  4  |  5  |  6  |  7  |  8  |  9  |  A  |  B  |  C  |  D  |  E  |  F  |     ]]
[0]=--[[ 0 ]]     imp,  inx,  imp,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  acc,  imm,  abs,  abs,  abs,  abs,  --[[ 0 ]]
    --[[ 1 ]]     rel,  inx,  imp,  inx,  zex,  zex,  zex,  zex,  imp,  aby,  imp,  aby,  abx,  abx,  abx,  abx,  --[[ 1 ]]
    --[[ 2 ]]     abs,  inx,  imp,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  acc,  imm,  abs,  abs,  abs,  abs,  --[[ 2 ]]
    --[[ 3 ]]     rel,  inx,  imp,  inx,  zex,  zex,  zex,  zex,  imp,  aby,  imp,  aby,  abx,  abx,  abx,  abx,  --[[ 3 ]]
    --[[ 4 ]]     imp,  inx,  imp,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  acc,  imm,  abs,  abs,  abs,  abs,  --[[ 4 ]]
    --[[ 5 ]]     rel,  inx,  imp,  inx,  zex,  zex,  zex,  zex,  imp,  aby,  imp,  aby,  abx,  abx,  abx,  abx,  --[[ 5 ]]
    --[[ 6 ]]     imp,  inx,  imp,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  acc,  imm,  abi,  abs,  abs,  abs,  --[[ 6 ]]
    --[[ 7 ]]     rel,  inx,  imp,  inx,  zex,  zex,  zex,  zex,  imp,  aby,  imp,  aby,  abx,  abx,  abx,  abx,  --[[ 7 ]]
    --[[ 8 ]]     imm,  inx,  imm,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  imp,  imm,  abs,  abs,  abs,  abs,  --[[ 8 ]]
    --[[ 9 ]]     rel,  inx,  imp,  inx,  zex,  zex,  zey,  zey,  imp,  aby,  imp,  aby,  abx,  abx,  aby,  aby,  --[[ 9 ]]
    --[[ A ]]     imm,  inx,  imm,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  imp,  imm,  abs,  abs,  abs,  abs,  --[[ A ]]
    --[[ B ]]     rel,  inx,  imp,  inx,  zex,  zex,  zey,  zey,  imp,  aby,  imp,  aby,  abx,  abx,  aby,  aby,  --[[ B ]]
    --[[ C ]]     imm,  inx,  imm,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  imp,  imm,  abs,  abs,  abs,  abs,  --[[ C ]]
    --[[ D ]]     rel,  inx,  imp,  inx,  zex,  zex,  zex,  zex,  imp,  aby,  imp,  aby,  abx,  abx,  abx,  abx,  --[[ D ]]
    --[[ E ]]     imm,  inx,  imm,  inx,  zer,  zer,  zer,  zer,  imp,  imm,  imp,  imm,  abs,  abs,  abs,  abs,  --[[ E ]]
    --[[ F ]]     rel,  inx,  imp,  inx,  zex,  zex,  zex,  zex,  imp,  aby,  imp,  aby,  abx,  abx,  abx,  abx   --[[ F ]]
}
opt = {
    --[[        |  0  |  1  |  2  |  3  |  4  |  5  |  6  |  7  |  8  |  9  |  A  |  B  |  C  |  D  |  E  |  F  |      ]]
[0]=--[[ 0 ]]      brk,  ora,  nop,  slo,  nop,  ora,  asl,  slo,  php,  ora,  asl,  nop,  nop,  ora,  asl,  slo, --[[ 0 ]]
    --[[ 1 ]]      bpl,  ora,  nop,  slo,  nop,  ora,  asl,  slo,  clc,  ora,  nop,  slo,  nop,  ora,  asl,  slo, --[[ 1 ]]
    --[[ 2 ]]      jsr,  ano,  nop,  rla,  bit,  ano,  rol,  rla,  plp,  ano,  rol,  nop,  bit,  ano,  rol,  rla, --[[ 2 ]]
    --[[ 3 ]]      bmi,  ano,  nop,  rla,  nop,  ano,  rol,  rla,  sec,  ano,  nop,  rla,  nop,  ano,  rol,  rla, --[[ 3 ]]
    --[[ 4 ]]      rti,  eor,  nop,  sre,  nop,  eor,  lsr,  sre,  pha,  eor,  lsr,  nop,  jmp,  eor,  lsr,  sre, --[[ 4 ]]
    --[[ 5 ]]      bvc,  eor,  nop,  sre,  nop,  eor,  lsr,  sre,  cli,  eor,  nop,  sre,  nop,  eor,  lsr,  sre, --[[ 5 ]]
    --[[ 6 ]]      rts,  adc,  nop,  rra,  nop,  adc,  ror,  rra,  pla,  adc,  ror,  nop,  jmp,  adc,  ror,  rra, --[[ 6 ]]
    --[[ 7 ]]      bvs,  adc,  nop,  rra,  nop,  adc,  ror,  rra,  sei,  adc,  nop,  rra,  nop,  adc,  ror,  rra, --[[ 7 ]]
    --[[ 8 ]]      nop,  sta,  nop,  sax,  sty,  sta,  stx,  sax,  dey,  nop,  txa,  nop,  sty,  sta,  stx,  sax, --[[ 8 ]]
    --[[ 9 ]]      bcc,  sta,  nop,  nop,  sty,  sta,  stx,  sax,  tya,  sta,  txs,  nop,  nop,  sta,  nop,  nop, --[[ 9 ]]
    --[[ A ]]      ldy,  lda,  ldx,  lax,  ldy,  lda,  ldx,  lax,  tay,  lda,  tax,  nop,  ldy,  lda,  ldx,  lax, --[[ A ]]
    --[[ B ]]      bcs,  lda,  nop,  lax,  ldy,  lda,  ldx,  lax,  clv,  lda,  tsx,  lax,  ldy,  lda,  ldx,  lax, --[[ B ]]
    --[[ C ]]      cpy,  cmp,  nop,  dcp,  cpy,  cmp,  dec,  dcp,  iny,  cmp,  dex,  nop,  cpy,  cmp,  dec,  dcp, --[[ C ]]
    --[[ D ]]      bne,  cmp,  nop,  dcp,  nop,  cmp,  dec,  dcp,  cld,  cmp,  nop,  dcp,  nop,  cmp,  dec,  dcp, --[[ D ]]
    --[[ E ]]      cpx,  sbc,  nop,  isb,  cpx,  sbc,  inc,  isb,  inx,  sbc,  nop,  sbc,  cpx,  sbc,  inc,  isb, --[[ E ]]
    --[[ F ]]      beq,  sbc,  nop,  isb,  nop,  sbc,  inc,  isb,  sed,  sbc,  nop,  isb,  nop,  sbc,  inc,  isb  --[[ F ]]
}

return function (r, w)
    read = r
    write = w

    return {
        nmi = nmi, 
        irq = irq, 
        reset = reset, 
        run = run
    }
end
