const pop = Math.popcount32(0xaaaaaaaa);
const ctzZero = Math.ctz32(0);
const ctz12 = Math.ctz32(12);
print("popcount32(0xaaaaaaaa)=" + pop + ", ctz32(0)=" + ctzZero + ", ctz32(12)=" + ctz12);
