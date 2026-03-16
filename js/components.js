/**
 * Church of Coherence — Shared nav and footer
 */
(function () {
  const base = document.querySelector('meta[name="base-path"]')?.getAttribute('content') || '';

  const navHTML = `
    <nav class="nav">
      <a href="${base}index.html" class="logo">Church of Coherence</a>
      <ul class="nav-links">
        <li><a href="${base}about.html">About</a></li>
        <li><a href="${base}teachings/index.html">Teachings</a></li>
        <li><a href="${base}traditions.html">Traditions</a></li>
        <li><a href="${base}practice.html">Practice</a></li>
        <li><a href="${base}resources.html">Resources</a></li>
        <li><a href="${base}contact.html">Contact</a></li>
      </ul>
      <button class="nav-toggle" aria-label="Toggle menu" aria-expanded="false">
        <span></span><span></span><span></span>
      </button>
    </nav>
    <div class="mobile-overlay" role="dialog" aria-label="Navigation menu">
      <a href="${base}index.html">Home</a>
      <a href="${base}about.html">About</a>
      <a href="${base}teachings/index.html">Teachings</a>
      <a href="${base}traditions.html">Traditions</a>
      <a href="${base}practice.html">Practice</a>
      <a href="${base}community.html">Community</a>
      <a href="${base}resources.html">Resources</a>
      <a href="${base}contact.html">Contact</a>
    </div>
  `;

  const footerHTML = `
    <footer>
      <p><a href="${base}index.html" style="color:var(--accent);text-decoration:none;font-family:var(--serif);font-size:1.1rem;">Church of Coherence</a></p>
      <p style="margin-top:0.5rem;opacity:0.7;">Built on the Coherence framework</p>
      <p class="footer-links" style="margin-top:0.75rem;">
        <a href="${base}about.html">About</a> ·
        <a href="${base}teachings/index.html">Teachings</a> ·
        <a href="${base}traditions.html">Traditions</a> ·
        <a href="${base}contact.html">Contact</a>
      </p>
    </footer>
  `;

  const navEl = document.getElementById('nav-placeholder');
  const footerEl = document.getElementById('footer-placeholder');
  if (navEl) navEl.innerHTML = navHTML;
  if (footerEl) footerEl.innerHTML = footerHTML;
})();
