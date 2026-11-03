// Checks that arithmetic which may wrap around (no nsw: unsigned code) is
// not assumed to stay within mathematical bounds. The multiplication below
// overflows 32 bits; the analysis must give up on it (full range), so the
// shift gets [0, 255] and not a bound above 2^32.
unsigned hash_top_byte(unsigned x) { return (x * 2654435761u) >> 24; }

// Signed overflow is undefined behavior (nsw), so here the analysis may keep
// computing over mathematical integers.
int scaled(signed char c) { return c * 1000; }   // [-128000, 127000]
