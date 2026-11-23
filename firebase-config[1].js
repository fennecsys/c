/* Firebase settings (public values: the security comes from firestore.rules, not from hiding these).
   Leave projectId empty to switch client editing off: pages then work exactly as before. */
window.FB_CONFIG = {
    projectId: "qr-code-pro-fbc50",
    apiKey: "AIzaSyClSGtealXiPRHjm8uivb5f164hiThdQmo",
    emailDomain: "clients.fennecsys.app"   // must be the same value as CLIENT_EMAIL_DOMAIN in main.py
};
