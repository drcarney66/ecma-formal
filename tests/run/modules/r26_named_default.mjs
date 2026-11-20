// `export default function g() {}` binds g locally and exports it as "default".
export default function g() { return typeof g; }
