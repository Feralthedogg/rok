//! Stack overflow on wasm32: exhausting the engine's call stack, or the
//! linear-memory stack (the main one placed first, so it runs off
//! address 0), traps, and code inside the module cannot catch a trap;
//! the host reports it. The guard range stays unknown (`[0, 0)`).

pub const fn thread_start() {}

pub const fn thread_exit() {}
