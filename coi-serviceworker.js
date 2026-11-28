/*! coi-serviceworker v0.1.7 - Guido Zuidhof and contributors, licensed under MIT */
let coepCredentialless = false;
if (typeof window === 'undefined') {
    self.addEventListener("install", () => self.skipWaiting());
    self.addEventListener("activate", (event) => event.waitUntil(self.clients.claim()));

    self.addEventListener("message", (ev) => {
        if (!ev.data) {
            return;
        } else if (ev.data.type === "deregister") {
            self.registration
                .unregister()
                .then(() => {
                    return self.clients.matchAll();
                })
                .then(clients => {
                    clients.forEach((client) => client.navigate(client.url));
                });
        } else if (ev.data.type === "coepCredentialless") {
            coepCredentialless = ev.data.value;
        }
    });

    self.addEventListener("fetch", function (event) {
        const r = event.request;
        if (r.cache === "only-if-cached" && r.mode !== "same-origin") {
            return;
        }

        const request = (coepCredentialless && r.mode === "no-cors")
            ? new Request(r, {
                credentials: "omit",
            })
            : r;
        event.respondWith(
            fetch(request)
                .then((response) => {
                    if (response.status === 0) {
                        return response;
                    }

                    const newHeaders = new Headers(response.headers);
                    newHeaders.set("Cross-Origin-Embedder-Policy",
                        coepCredentialless ? "credentialless" : "require-corp"
                    );
                    if (!coepCredentialless) {
                        newHeaders.set("Cross-Origin-Resource-Policy", "cross-origin");
                    }
                    newHeaders.set("Cross-Origin-Opener-Policy", "same-origin");

                    return new Response(response.body, {
                        status: response.status,
                        statusText: response.statusText,
                        headers: newHeaders,
                    });
                })
                .catch((e) => console.error(e))
        );
    });

} else {
    (() => {
        // Always use COEP: require-corp (supported across Chrome, Firefox, and Safari; credentialless is ignored by Safari).
        const coi = {
            shouldRegister: () => true,
            shouldDeregister: () => false,
            coepCredentialless: () => false,
            doReload: () => window.location.reload(),
            quiet: false,
            ...window.coi
        };

        const n = navigator;
        const scriptSrc = window.document.currentScript && window.document.currentScript.src;

        if (n.serviceWorker && n.serviceWorker.controller) {
            n.serviceWorker.controller.postMessage({
                type: "coepCredentialless",
                value: coi.coepCredentialless(),
            });

            if (coi.shouldDeregister()) {
                n.serviceWorker.controller.postMessage({ type: "deregister" });
            }
        }

        if (window.crossOriginIsolated) {
            try {
                sessionStorage.removeItem("coiReloadedBySelf");
                sessionStorage.removeItem("coiTopReloaded");
                if (scriptSrc && n.serviceWorker && n.serviceWorker.getRegistrations) {
                    const rootScope = new URL("./", scriptSrc).href;
                    n.serviceWorker.getRegistrations().then((regs) => {
                        for (const reg of regs) {
                            if (reg.scope !== rootScope && reg.scope.startsWith(rootScope)) {
                                reg.unregister();
                            }
                        }
                    });
                }
            } catch (e) { /* ignore */ }
            return;
        }

        if (window.crossOriginIsolated !== false || !coi.shouldRegister()) return;

        if (!window.isSecureContext) {
            !coi.quiet && console.log("COOP/COEP Service Worker not registered, a secure context is required.");
            return;
        }

        if (!n.serviceWorker || !scriptSrc) return;

        let reloading = false;
        const reloadOnce = () => {
            if (reloading) return;
            reloading = true;
            try {
                if (window.self !== window.top && window.top && window.top.crossOriginIsolated === false) {
                    if (!sessionStorage.getItem("coiTopReloaded")) {
                        sessionStorage.setItem("coiTopReloaded", "1");
                        window.top.location.reload();
                        return;
                    }
                }
            } catch (e) { /* ignore */ }
            coi.doReload();
        };

        // If a controller already claims this page yet crossOriginIsolated is still false (e.g. claimed mid-load
        // or switching from an older narrow-scope worker), reload once so the fetch handler supplies COOP/COEP.
        if (n.serviceWorker.controller) {
            try {
                if (!sessionStorage.getItem("coiReloadedBySelf")) {
                    sessionStorage.setItem("coiReloadedBySelf", "1");
                    reloadOnce();
                    return;
                }
            } catch (e) { /* ignore */ }
        }

        n.serviceWorker.addEventListener("controllerchange", () => {
            !coi.quiet && console.log("Reloading page after COOP/COEP Service Worker claimed control.");
            reloadOnce();
        });

        n.serviceWorker.register(scriptSrc).then(
            (registration) => {
                !coi.quiet && console.log("COOP/COEP Service Worker registered", registration.scope);

                const watchWorker = (w) => {
                    if (!w) return;
                    w.addEventListener("statechange", () => {
                        if (w.state === "activated" && !window.crossOriginIsolated) reloadOnce();
                    });
                };
                watchWorker(registration.installing || registration.waiting);

                registration.addEventListener("updatefound", () => {
                    watchWorker(registration.installing);
                });

                if (registration.active && !n.serviceWorker.controller) {
                    !coi.quiet && console.log("Reloading page to make use of COOP/COEP Service Worker.");
                    reloadOnce();
                }
            },
            (err) => {
                !coi.quiet && console.error("COOP/COEP Service Worker failed to register:", err);
            }
        );
    })();
}
