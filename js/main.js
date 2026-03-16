/**
 * Church of Coherence
 * Animation system, scroll effects, and interactivity
 */

document.addEventListener('DOMContentLoaded', () => {

  // --- Scroll Progress Bar ---
  const progressBar = document.createElement('div');
  progressBar.className = 'scroll-progress';
  document.body.prepend(progressBar);

  function updateProgress() {
    const scrollTop = window.scrollY;
    const docHeight = document.documentElement.scrollHeight - window.innerHeight;
    const progress = docHeight > 0 ? (scrollTop / docHeight) * 100 : 0;
    progressBar.style.width = progress + '%';
  }

  // --- Reveal Animations (IntersectionObserver) ---
  const revealObserver = new IntersectionObserver(
    (entries) => {
      entries.forEach((entry) => {
        if (entry.isIntersecting) {
          entry.target.classList.add('revealed');
        }
      });
    },
    { threshold: 0.08, rootMargin: '0px 0px -40px 0px' }
  );

  document.querySelectorAll('.section, .reveal, .reveal-left, .reveal-right, .reveal-scale').forEach((el) => {
    if (!el.classList.contains('reveal') && !el.classList.contains('reveal-left') &&
        !el.classList.contains('reveal-right') && !el.classList.contains('reveal-scale')) {
      el.classList.add('reveal');
    }
    revealObserver.observe(el);
  });

  document.querySelectorAll('.stagger-children').forEach((el) => {
    revealObserver.observe(el);
  });

  document.querySelectorAll('.timeline-event').forEach((el) => {
    revealObserver.observe(el);
  });

  // --- Phi Counter Animation ---
  const phiCounter = document.querySelector('.phi-counter');
  if (phiCounter) {
    let counted = false;
    const phiObserver = new IntersectionObserver(
      (entries) => {
        entries.forEach((entry) => {
          if (entry.isIntersecting && !counted) {
            counted = true;
            animatePhiCounter(phiCounter);
          }
        });
      },
      { threshold: 0.3 }
    );
    phiObserver.observe(phiCounter);
  }

  function animatePhiCounter(el) {
    const prefix = 'φ = ';
    const target = '1.618034...';
    let i = 0;
    el.textContent = prefix;
    const interval = setInterval(() => {
      if (i <= target.length) {
        el.textContent = prefix + target.substring(0, i);
        i++;
      } else {
        clearInterval(interval);
      }
    }, 120);
  }

  // --- Floating Section Nav ---
  const floatingNav = document.querySelector('.floating-nav');
  if (floatingNav) {
    const navLinks = floatingNav.querySelectorAll('a');
    const sections = [];

    navLinks.forEach((link) => {
      const href = link.getAttribute('href');
      if (href && href.startsWith('#')) {
        const section = document.querySelector(href);
        if (section) sections.push({ link, section });
      }
    });

    function updateFloatingNav() {
      const scrollTop = window.scrollY + window.innerHeight / 3;

      if (window.scrollY > 300) {
        floatingNav.classList.add('visible');
      } else {
        floatingNav.classList.remove('visible');
      }

      let activeIndex = -1;
      sections.forEach((item, index) => {
        const top = item.section.offsetTop;
        const bottom = top + item.section.offsetHeight;
        if (scrollTop >= top && scrollTop < bottom) {
          activeIndex = index;
        }
      });

      navLinks.forEach((link, index) => {
        link.classList.toggle('active', index === activeIndex);
      });
    }

    window.addEventListener('scroll', updateFloatingNav, { passive: true });
    updateFloatingNav();
  }

  // --- Tradition Tabs Active State ---
  const traditionTabs = document.querySelector('.tradition-tabs');
  if (traditionTabs) {
    const tabLinks = traditionTabs.querySelectorAll('.tradition-tab');
    const traditionSections = ['#buddhism', '#christianity', '#islam', '#synthesis'];

    function updateTraditionTabs() {
      const scrollTop = window.scrollY + 150;
      let activeIndex = -1;
      traditionSections.forEach((id, index) => {
        const section = document.querySelector(id);
        if (section) {
          const top = section.offsetTop;
          const bottom = top + section.offsetHeight;
          if (scrollTop >= top && scrollTop < bottom) activeIndex = index;
        }
      });
      tabLinks.forEach((link, index) => {
        link.classList.toggle('active', index === activeIndex);
      });
    }
    window.addEventListener('scroll', updateTraditionTabs, { passive: true });
    updateTraditionTabs();
  }

  // --- Smooth Scroll for Anchor Links ---
  document.querySelectorAll('a[href^="#"]').forEach((anchor) => {
    anchor.addEventListener('click', function (e) {
      const target = document.querySelector(this.getAttribute('href'));
      if (target) {
        e.preventDefault();
        target.scrollIntoView({ behavior: 'smooth', block: 'start' });
      }
    });
  });

  // --- Parallax-lite for Hero ---
  const hero = document.querySelector('.hero');
  const heroContent = document.querySelector('.hero-content');
  if (hero && heroContent) {
    function updateParallax() {
      const scrollTop = window.scrollY;
      if (scrollTop < window.innerHeight) {
        const offset = scrollTop * 0.15;
        heroContent.style.transform = `translateY(${offset}px)`;
        heroContent.style.opacity = Math.max(0, 1 - scrollTop / (window.innerHeight * 0.8));
      }
    }
    window.addEventListener('scroll', updateParallax, { passive: true });
  }

  // --- Card Tilt Micro-interaction ---
  document.querySelectorAll('.answer-card, .crisis-card, .phi-fact, .teaching-card, .journey-card').forEach((card) => {
    card.addEventListener('mousemove', (e) => {
      const rect = card.getBoundingClientRect();
      const x = e.clientX - rect.left;
      const y = e.clientY - rect.top;
      const centerX = rect.width / 2;
      const centerY = rect.height / 2;
      const rotateX = (y - centerY) / centerY * -2;
      const rotateY = (x - centerX) / centerX * 2;
      card.style.transform = `translateY(-4px) perspective(800px) rotateX(${rotateX}deg) rotateY(${rotateY}deg)`;
    });

    card.addEventListener('mouseleave', () => {
      card.style.transform = '';
    });
  });

  // --- Mobile Nav Toggle ---
  const navToggle = document.querySelector('.nav-toggle');
  const mobileOverlay = document.querySelector('.mobile-overlay');
  if (navToggle && mobileOverlay) {
    navToggle.addEventListener('click', () => {
      navToggle.classList.toggle('active');
      mobileOverlay.classList.toggle('active');
      document.body.style.overflow = mobileOverlay.classList.contains('active') ? 'hidden' : '';
    });

    mobileOverlay.querySelectorAll('a').forEach((link) => {
      link.addEventListener('click', () => {
        navToggle.classList.remove('active');
        mobileOverlay.classList.remove('active');
        document.body.style.overflow = '';
      });
    });
  }

  // --- Back to Top Button ---
  const backToTop = document.createElement('a');
  backToTop.href = '#';
  backToTop.className = 'back-to-top';
  backToTop.setAttribute('aria-label', 'Back to top');
  backToTop.innerHTML = '<svg viewBox="0 0 24 24" fill="none" stroke="currentColor" stroke-width="2"><path d="M12 19V5M5 12l7-7 7 7"/></svg>';
  document.body.appendChild(backToTop);

  backToTop.addEventListener('click', (e) => {
    e.preventDefault();
    window.scrollTo({ top: 0, behavior: 'smooth' });
  });

  function updateBackToTop() {
    if (window.scrollY > 600) {
      backToTop.classList.add('visible');
    } else {
      backToTop.classList.remove('visible');
    }
  }

  window.addEventListener('scroll', updateBackToTop, { passive: true });
  updateBackToTop();

  // --- Scroll listener (throttled) ---
  let ticking = false;
  window.addEventListener('scroll', () => {
    if (!ticking) {
      requestAnimationFrame(() => {
        updateProgress();
        updateBackToTop();
        ticking = false;
      });
      ticking = true;
    }
  }, { passive: true });

  updateProgress();
});
