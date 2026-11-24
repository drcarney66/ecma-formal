// ECMA-262 in Lean: the theme switch, the filter of the table of laws, folding the Lean, the table of contents'
// current entry. Every page reads in full without it.
(function () {
  "use strict";
  var root = document.documentElement;
  root.classList.add("js");

  function load(k) { try { return localStorage.getItem(k); } catch (e) { return null; } }
  function save(k, v) { try { if (v === null) localStorage.removeItem(k); else localStorage.setItem(k, v); } catch (e) { /* none */ } }

  // Default to light mode; toggle between light and dark.
  var order = ["light", "dark"];
  function apply(t) {
    var mode = t === "dark" ? "dark" : "light";
    root.setAttribute("data-theme", mode);
    var label = mode === "dark" ? "Switch to light mode" : "Switch to dark mode";
    ["theme", "corner-theme"].forEach(function (id) {
      var b = document.getElementById(id);
      if (b) b.title = label;
    });
  }
  var theme = load("theme") === "dark" ? "dark" : "light";
  apply(theme);

  document.addEventListener("DOMContentLoaded", function () {
    apply(theme);
    var toggleTheme = function () {
      theme = theme === "dark" ? "light" : "dark";
      save("theme", theme);
      apply(theme);
    };
    var b = document.getElementById("theme");
    if (b) b.addEventListener("click", toggleTheme);
    var cb = document.getElementById("corner-theme");
    if (cb) cb.addEventListener("click", toggleTheme);

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

    // 16:9 slide deck with intra-slide step animations, control-free present mode, and live debugger overlay.
    var deck = document.getElementById("deck");
    if (deck) {
      var slides = Array.prototype.slice.call(deck.querySelectorAll(".slide"));
      var posEl = document.getElementById("deck-pos");
      var prevBtn = document.getElementById("deck-prev");
      var nextBtn = document.getElementById("deck-next");
      var presBtn = document.getElementById("deck-present");
      var modal = document.getElementById("dbg-modal");
      var modalFrame = document.getElementById("dbg-modal-frame");
      var modalClose = document.getElementById("dbg-modal-close");
      var step3Frame = document.getElementById("step3-dbg-frame");
      var idx = 0;
      var step = 0;
      var presenting = new URLSearchParams(location.search).has("present");

      var maxStepOf = function (i) {
        return parseInt(slides[i].getAttribute("data-max-step") || "0", 10) || 0;
      };

      var syncDeck = function () {
        slides.forEach(function (s, i) {
          s.classList.toggle("active", i === idx);
          if (i === idx) s.setAttribute("data-step", String(step));
        });
        root.classList.toggle("deck-present", presenting);
        if (posEl) posEl.textContent = (idx + 1) + " / " + slides.length;
        if (prevBtn) prevBtn.disabled = idx === 0 && step === 0;
        if (nextBtn) nextBtn.disabled = idx === slides.length - 1 && step >= maxStepOf(idx);
        // Lazy-load the inline Step 3 live debugger iframe only when revealed.
        if (step3Frame && slides[idx].id === "slide-step-3" && step >= 1 && !step3Frame.getAttribute("src")) {
          var ssrc = step3Frame.getAttribute("data-dbg-src");
          if (ssrc) step3Frame.setAttribute("src", ssrc);
        }
      };

      var advance = function () {
        var m = maxStepOf(idx);
        if (step < m) { step++; syncDeck(); }
        else if (idx < slides.length - 1) { idx++; step = 0; syncDeck(); }
      };

      var retreat = function () {
        if (step > 0) { step--; syncDeck(); }
        else if (idx > 0) { idx--; step = maxStepOf(idx); syncDeck(); }
      };

      var setPresent = function (on) {
        presenting = on;
        syncDeck();
      };

      var openDbgModal = function (url) {
        if (!modal || !modalFrame || !url) return;
        modalFrame.setAttribute("src", url);
        modal.hidden = false;
      };

      var closeDbgModal = function () {
        if (!modal || modal.hidden) return false;
        modal.hidden = true;
        if (modalFrame) modalFrame.removeAttribute("src");
        window.focus();
        return true;
      };

      if (prevBtn) prevBtn.addEventListener("click", retreat);
      if (nextBtn) nextBtn.addEventListener("click", advance);
      if (presBtn) presBtn.addEventListener("click", function () { setPresent(true); });
      if (modalClose) modalClose.addEventListener("click", closeDbgModal);
      if (modal) modal.addEventListener("click", function (e) { if (e.target === modal) closeDbgModal(); });

      document.addEventListener("click", function (e) {
        var trigger = e.target.closest ? e.target.closest("[data-dbg-open]") : null;
        if (trigger && !e.metaKey && !e.ctrlKey && !e.shiftKey) {
          e.preventDefault();
          e.stopPropagation();
          openDbgModal(trigger.getAttribute("data-dbg-open"));
        }
      });

      document.addEventListener("keydown", function (e) {
        if (e.altKey || e.ctrlKey || e.metaKey) return;
        if (modal && !modal.hidden) {
          if (e.key === "Escape") { e.preventDefault(); closeDbgModal(); }
          return;
        }
        var tag = e.target && e.target.tagName;
        if (tag === "INPUT" || tag === "TEXTAREA" || tag === "SELECT") return;
        if (e.key === "Enter" && e.target && e.target.hasAttribute && e.target.hasAttribute("data-dbg-open")) {
          e.preventDefault();
          openDbgModal(e.target.getAttribute("data-dbg-open"));
          return;
        }
        if (e.key === "Escape") {
          if (presenting) { e.preventDefault(); setPresent(false); }
        } else if (e.key === "f" || e.key === "F") {
          e.preventDefault();
          setPresent(!presenting);
        } else if (e.key === "ArrowRight" || e.key === "PageDown" || (e.key === " " && tag !== "BUTTON" && tag !== "A")) {
          e.preventDefault();
          advance();
        } else if (e.key === "ArrowLeft" || e.key === "PageUp") {
          e.preventDefault();
          retreat();
        } else if (e.key === "Home") {
          e.preventDefault();
          idx = 0; step = 0; syncDeck();
        } else if (e.key === "End") {
          e.preventDefault();
          idx = slides.length - 1; step = maxStepOf(idx); syncDeck();
        }
      });

      window.addEventListener("message", function (e) {
        if (e.origin !== location.origin || !e.data) return;
        if (e.data.type === "deck-escape") {
          if (!closeDbgModal() && presenting) setPresent(false);
        }
      });

      syncDeck();
    }
  });
})();
