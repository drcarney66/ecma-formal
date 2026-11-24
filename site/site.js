// ECMA-262 in Lean: the theme switch, the filter of the table of laws, folding the Lean, the table of contents'
// current entry. Every page reads in full without it.
(function () {
  "use strict";
  var root = document.documentElement;
  root.classList.add("js");

  function load(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
  function save(k, v) { try { if (v === null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) { /* none */ } }

  // The theme: follow the system, or light, or dark.
  var order = [null, "light", "dark"];
  var names = { "null": "Auto", light: "Light", dark: "Dark" };
  function apply(t) {
    if (t) root.setAttribute("data-theme", t); else root.removeAttribute("data-theme");
    var b = document.getElementById("theme");
    if (b) {
      b.querySelector(".theme-label").textContent = names[String(t)];
      b.title = "Colour theme: " + (t ? t : "follows the system") + " (select to change)";
    }
  }
  var theme = load("theme");
  if (order.indexOf(theme) < 0) theme = null;
  apply(theme);

  document.addEventListener("DOMContentLoaded", function () {
    apply(theme);
    var b = document.getElementById("theme");
    if (b) b.addEventListener("click", function () {
      theme = order[(order.indexOf(theme) + 1) % order.length];
      save("theme", theme);
      apply(theme);
    });

    // The table of laws: rows whose text has every word typed.
    var input = document.getElementById("lawfilter");
    if (input) {
      var rows = Array.prototype.slice.call(document.querySelectorAll(".lawtable tbody tr"));
      var count = document.querySelector(".filter-count");
      var run = function () {
        var words = input.value.toLowerCase().split(/\s+/).filter(Boolean);
        var shown = 0;
        rows.forEach(function (r) {
          var q = r.getAttribute("data-q");
          var ok = words.every(function (w) { return q.indexOf(w) >= 0; });
          r.hidden = !ok;
          if (ok) shown++;
        });
        count.textContent = words.length ? shown + " of " + rows.length : "";
      };
      input.addEventListener("input", run);
      run();
    }

    // Folding: one control to open or close every fold of the page.
    var folds = Array.prototype.slice.call(document.querySelectorAll("details.lean-fold"));
    var title = document.querySelector("main > header.title");
    if (folds.length > 3 && title) {
      var p = document.createElement("p");
      p.className = "foldall";
      var btn = document.createElement("button");
      btn.type = "button";
      btn.className = "theme";
      btn.id = "foldall";
      var set = function (open) {
        folds.forEach(function (d) { d.open = open; });
        btn.textContent = open ? "Fold all Lean" : "Show all Lean (" + folds.length + ")";
        btn.setAttribute("aria-pressed", open ? "true" : "false");
      };
      var open = load("lean-open") === "1";
      set(open);
      btn.addEventListener("click", function () { open = !open; save("lean-open", open ? "1" : null); set(open); });
      p.appendChild(btn);
      title.appendChild(p);
    }

    // A link into a folded part opens it.
    var reveal = function () {
      var id = decodeURIComponent(location.hash.slice(1));
      var el = id && document.getElementById(id);
      for (var e = el; e; e = e.parentElement) if (e.tagName === "DETAILS") e.open = true;
    };
    window.addEventListener("hashchange", reveal);
    reveal();

    // Printing shows every fold.
    var closed = [];
    window.addEventListener("beforeprint", function () {
      closed = folds.filter(function (d) { return !d.open; });
      closed.forEach(function (d) { d.open = true; });
    });
    window.addEventListener("afterprint", function () { closed.forEach(function (d) { d.open = false; }); });

    // On a narrow screen the table of contents starts folded: it sits above the text.
    // On a narrow screen the pages fold behind "Pages", which opens over the text and closes on Escape or a
    // click elsewhere. (The breakpoint is style.css's.)
    var navd = document.getElementById("nav-details");
    var narrow = window.matchMedia ? window.matchMedia("(max-width: 61.99rem)") : null;
    if (navd && narrow) {
      var fit = function () { navd.open = !narrow.matches; };
      fit();
      if (narrow.addEventListener) narrow.addEventListener("change", fit);
      document.addEventListener("click", function (e) { if (narrow.matches && navd.open && !navd.contains(e.target)) navd.open = false; });
      document.addEventListener("keydown", function (e) { if (e.key === "Escape" && narrow.matches && navd.open) navd.open = false; });
    }

    var tocd = document.getElementById("toc-details");
    if (tocd && window.matchMedia && window.matchMedia("(max-width: 69.99rem)").matches) tocd.open = false;

    // The table of contents marks the part being read.
    var toc = document.querySelector(".toc");
    if (toc && "IntersectionObserver" in window) {
      var links = {};
      Array.prototype.forEach.call(toc.querySelectorAll("a"), function (a) { links[decodeURIComponent(a.hash.slice(1))] = a; });
      var current = null;
      var obs = new IntersectionObserver(function (entries) {
        entries.forEach(function (en) {
          if (en.isIntersecting && links[en.target.id]) {
            if (current) current.classList.remove("here");
            current = links[en.target.id];
            current.classList.add("here");
          }
        });
      }, { rootMargin: "-10% 0px -80% 0px" });
      Object.keys(links).forEach(function (id) { var el = document.getElementById(id); if (el) obs.observe(el); });
    }

    // Slide deck controls and single-slide presentation mode (slides.html).
    var deck = document.getElementById("deck");
    if (deck) {
      var slides = Array.prototype.slice.call(deck.querySelectorAll(".slide"));
      var posEl = document.getElementById("deck-pos");
      var fillEl = document.getElementById("deck-progress-fill");
      var prevBtn = document.getElementById("deck-prev");
      var nextBtn = document.getElementById("deck-next");
      var presBtn = document.getElementById("deck-present");
      var idx = 0;
      var presenting = false;
      var syncDeck = function () {
        slides.forEach(function (s, i) { s.classList.toggle("active", i === idx); });
        if (posEl) posEl.textContent = "Slide " + (idx + 1) + " / " + slides.length;
        if (fillEl) fillEl.style.width = (((idx + 1) / slides.length) * 100).toFixed(1) + "%";
        if (prevBtn) prevBtn.disabled = idx === 0;
        if (nextBtn) nextBtn.disabled = idx === slides.length - 1;
        if (presBtn) {
          presBtn.setAttribute("aria-pressed", presenting ? "true" : "false");
          presBtn.textContent = presenting ? "Exit present (Esc)" : "Present";
        }
      };
      var goTo = function (n) {
        idx = Math.max(0, Math.min(slides.length - 1, n));
        syncDeck();
        if (presenting) window.scrollTo(0, 0);
        else slides[idx].scrollIntoView({ behavior: "smooth", block: "start" });
      };
      var setPresent = function (on) {
        presenting = on;
        root.classList.toggle("deck-present", on);
        syncDeck();
        if (on) window.scrollTo(0, 0);
        else slides[idx].scrollIntoView({ block: "start" });
      };
      if (prevBtn) prevBtn.addEventListener("click", function () { goTo(idx - 1); });
      if (nextBtn) nextBtn.addEventListener("click", function () { goTo(idx + 1); });
      if (presBtn) presBtn.addEventListener("click", function () { setPresent(!presenting); });
      if ("IntersectionObserver" in window) {
        var sobs = new IntersectionObserver(function (entries) {
          if (presenting) return;
          entries.forEach(function (en) {
            if (en.isIntersecting) {
              var k = slides.indexOf(en.target);
              if (k >= 0) { idx = k; syncDeck(); }
            }
          });
        }, { rootMargin: "-20% 0px -55% 0px" });
        slides.forEach(function (s) { sobs.observe(s); });
      }
      document.addEventListener("keydown", function (e) {
        if (e.altKey || e.ctrlKey || e.metaKey) return;
        var tag = e.target && e.target.tagName;
        if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;
        if (e.key === "f" || e.key === "F") { e.preventDefault(); setPresent(!presenting); }
        else if (e.key === "Escape" && presenting) { e.preventDefault(); setPresent(false); }
        else if (e.key === "ArrowRight" || e.key === "PageDown" || (e.key === " " && tag !== "BUTTON" && tag !== "A")) {
          e.preventDefault(); goTo(idx + 1);
        } else if (e.key === "ArrowLeft" || e.key === "PageUp") {
          e.preventDefault(); goTo(idx - 1);
        } else if (e.key === "Home" && presenting) {
          e.preventDefault(); goTo(0);
        } else if (e.key === "End" && presenting) {
          e.preventDefault(); goTo(slides.length - 1);
        }
      });
      syncDeck();
    }
  });
})();
