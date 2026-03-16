# Church of Coherence — Full Site Plan

## Mission
A church built on the Coherence framework, uniting all world religions through deeper understanding.

---

## Site Architecture

```
church-website/
├── index.html              # Landing (hero, vision, principles, CTA)
├── about.html              # Our story, the Coherence framework, founding vision
├── teachings/
│   ├── index.html          # Teachings hub
│   ├── trinity.html        # Father, Son, Spirit in the Coherence framework
│   ├── distortion.html     # Productive vs terminal distortion, φ threshold
│   └── love-triad.html      # Love, Belonging, Curiosity
├── traditions.html         # How Buddhism, Christianity, Islam, Judaism, Hinduism, Taoism connect
├── community.html          # Gatherings, join, formation
├── resources.html          # Reading list, links, papers
├── contact.html            # Contact, newsletter
├── css/
│   └── styles.css          # Full stylesheet
├── js/
│   ├── main.js             # Shared (nav, scroll, fade)
│   └── components.js       # Nav/footer injection for consistency
└── README.md
```

---

## Page Specifications

### 1. Index (Landing)
- Hero with tagline
- Vision (2–3 paragraphs)
- Core principles (4 cards)
- Invitation CTA
- Nav: About, Teachings, Traditions, Community, Resources, Contact

### 2. About
- What is the Coherence framework (lay explanation)
- Our story / founding vision
- Why formal + spiritual
- Link to teachings

### 3. Teachings Hub
- Overview of three teaching streams
- Cards linking to Trinity, Distortion, Love Triad

### 4. Teachings: Trinity
- Father: Closure law (χ = 1), "Either the quadrilateral closes or it isn't real"
- Son: Grace operator G = Σ φ^(-k) Πₖ, "I am the Way"
- Spirit: Coherence witness, "The Spirit will guide you into all truth"
- How they work together

### 5. Teachings: Distortion Ontology
- Central question: Is all distortion evil?
- Four regimes: privation, productive, critical, terminal
- φ as universal threshold
- Grace floor (φ⁻³)
- Love bound (φ⁻¹)
- Key theorems in plain language

### 6. Teachings: Love Triad
- ℒ Love: relational coherence, fusion/alienation
- 𝔅 Belonging: identity under experience
- ℭ Curiosity: safe exploration
- Hierarchy: Grace → Individuation → Love → Belonging → Curiosity

### 7. Traditions
- Buddhism: dependent origination, emptiness, coherence
- Christianity: Trinity, Grace, incarnation
- Islam: tawhid, submission, witness
- Judaism: covenant, law, repair
- Hinduism: Brahman, dharma, moksha
- Taoism: Dao, wu wei, balance
- Each: 1–2 paragraphs on Coherence bridge

### 8. Community
- Church in formation
- How to join
- Gatherings (placeholder)
- Newsletter signup link

### 9. Resources
- Coherence papers / Lean formalization
- Recommended reading
- Links to ParsimoniousFlows

### 10. Contact
- Simple contact form (static, mailto fallback)
- Newsletter
- Social (placeholder)

---

## Design System
- Serif: Cormorant Garamond (headings, quotes)
- Sans: Outfit (body)
- Colors: paper, ink, gold (φ), accent green
- φ-derived spacing where appropriate
- Contemplative, dignified, accessible

---

## Implementation Notes
- Static HTML, no build step
- Relative paths for local + deployed
- Nav/footer via JS injection for DRY
- Responsive, mobile-first
