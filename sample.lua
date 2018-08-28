mem = {}
function read(a) return mem[a] end
function write(a, b) mem[a] = b end
mos = require("nes.src.cpu")(read, write)
for i = 0, 0xFFFF do
    write(i, i % 256)
end
write(0, 1)
mos.reset()
mos.run(100)
