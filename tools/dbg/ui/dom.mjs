// DOM helpers shared by the panes.

// A new element: its tag, class and text.
export function el(tag, cls, text) {
  const e = document.createElement(tag);
  if (cls) e.className = cls;
  if (text !== undefined) e.textContent = text;
  return e;
}

export const $ = (id) => document.getElementById(id);
