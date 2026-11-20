// args: --bundle --prelude tests/run/modules/mjsunit_shim.js
// expect: normal: undefined
// V8's test/mjsunit/d8/module-bundle-1.js, as it is below, its assertions from the mjsunit shim.
// Copyright 2026 the V8 project authors. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE file.

// Flags: --bundle

// JS_BUNDLE_MODULE:a.mjs
export {a}
let a = 42;

// JS_BUNDLE_MODULE:b.mjs
export * from "a.mjs"

// JS_BUNDLE_MODULE_ENTRYPOINT
import {a} from "b.mjs"
assertEquals(a, 42);
