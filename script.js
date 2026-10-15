'use strict';

/* ============================================================================
   گربه‌رقصان — اسکریپت اصلی
   ----------------------------------------------------------------------------
   فهرست:
     ۰) ابزارهای عمومی
     ۱) موتور تحلیل صدا (AudioEngine)
     ۲) سیستم سبک‌ها (STYLES)
     ۳) سیستم ذرات (Particles)
     ۴) تعریف گربه‌ها (CAT_DEFS)
     ۵) توابع کمکی رسم (اسکلت به‌هم‌پیوسته)
     ۶) کلاس گربه (Cat)
     ۷) صحنه و حلقه‌ی رندر
     ۸) پلیر (لود، پخش، تایم‌لاین، لیست)
     ۹) مودال انتخاب سبک
    ۱۰) راه‌اندازی
   ============================================================================ */


/* ============================================================================
   ۰) ابزارهای عمومی
   ============================================================================ */

const $ = s => document.querySelector(s);
const $$ = s => document.querySelectorAll(s);

/** عدد را با ارقام فارسی برمی‌گرداند */
const fa = n => Math.round(n).toLocaleString('fa-IR');

/** محدود کردن مقدار بین a و b */
const clamp = (v, a = 0, b = 1) => Math.min(b, Math.max(a, v));

/** زاویه را به بازهٔ [-π, π] می‌پیچد */
const wrap = a => Math.atan2(Math.sin(a), Math.cos(a));

/** درون‌یابی خطی */
const lerp = (a, b, t) => a + (b - a) * t;

/** عدد تصادفی در بازه */
const rand = (a, b) => a + Math.random() * (b - a);

/** هموارسازی نمایی مستقل از نرخ فریم */
const smooth = (cur, target, rate, dt) =>
  cur + (target - cur) * (1 - Math.exp(-dt * rate));

/** هموارسازی با نرخ attack/release متفاوت (برای حس ضربه‌ای) */
const smoothAR = (cur, target, attack, release, dt) =>
  cur + (target - cur) * (1 - Math.exp(-dt * (target > cur ? attack : release)));

/** پالی‌فیل برای roundRect (سازگاری با مرورگرهای قدیمی‌تر) */
if (!CanvasRenderingContext2D.prototype.roundRect) {
  CanvasRenderingContext2D.prototype.roundRect = function (x, y, w, h, r) {
    if (typeof r === 'number') r = [r, r, r, r];
    if (!Array.isArray(r)) r = [0, 0, 0, 0];
    const [tl, tr, br, bl] = r;
    this.moveTo(x + tl, y);
    this.lineTo(x + w - tr, y);
    this.quadraticCurveTo(x + w, y, x + w, y + tr);
    this.lineTo(x + w, y + h - br);
    this.quadraticCurveTo(x + w, y + h, x + w - br, y + h);
    this.lineTo(x + bl, y + h);
    this.quadraticCurveTo(x, y + h, x, y + h - bl);
    this.lineTo(x, y + tl);
    this.quadraticCurveTo(x, y, x + tl, y);
    return this;
  };
}


/* ============================================================================
   ۱) موتور تحلیل صدا
   ----------------------------------------------------------------------------
   دو مسیر موازی:
     • مسیر آنی: RMS، باندها، onset، گیت سکوت (پاسخ ~۳۰ms)
     • مسیر نرم: انرژی، وکال، رنگ (پاسخ ~۲۰۰ms)
   تشخیص وکال با باند ۳۰۰–۳۴۰۰ هرتز + گیت نسبت به bass.
   ============================================================================ */

class AudioEngine {
  constructor(el) {
    this.el = el;
    this.ctx = null;
    this.analyser = null;
    this.freq = null;
    this.time = null;
    this.prevFreq = null;
    this.connected = false;

    /* --- آنی --- */
    this.rms = 0;
    this.bass = 0;
    this.mid = 0;
    this.high = 0;
    this.vocalRaw = 0;   // انرژی خام باند وکال
    this.vocal = 0;      // وکال گیت‌شده
    this.flux = 0;
    this.silence = 1;    // ۱ = سکوت کامل، ۰ = پخش فعال

    /* --- نرم --- */
    this.sBass = 0;
    this.sMid = 0;
    this.sHigh = 0;
    this.sEnergy = 0;
    this.sVocal = 0;

    /* --- ضرب --- */
    this.bpm = 100;
    this.hasBpm = false;
    this.beat = 0;
    this.pulse = 0;
    this.onsets = [];
    this.lastOnset = -10;
    this.history = [];
  }

  /* اتصال به Web Audio API (یک‌بار) */
  connect() {
    if (this.connected) return;
    const AC = window.AudioContext || window.webkitAudioContext;
    if (!AC) return;
    this.ctx = new AC();
    this.analyser = this.ctx.createAnalyser();
    this.analyser.fftSize = 2048;
    // smoothing پایین = پاسخ آنی
    this.analyser.smoothingTimeConstant = 0.15;
    const src = this.ctx.createMediaElementSource(this.el);
    src.connect(this.analyser);
    this.analyser.connect(this.ctx.destination);
    this.freq = new Uint8Array(this.analyser.frequencyBinCount);
    this.time = new Float32Array(this.analyser.fftSize);
    this.prevFreq = new Float32Array(this.freq.length);
    this.connected = true;
  }

  /* از سرگیری context در صورت suspend */
  async resume() {
    if (this.ctx && this.ctx.state === 'suspended') {
      try { await this.ctx.resume(); } catch (e) {}
    }
  }

  /* میانگین یک باند فرکانسی */
  bandAvg(from, to) {
    let s = 0;
    for (let i = from; i < to; i++) s += this.freq[i];
    return s / ((to - from) * 255);
  }

  /* ---- به‌روزرسانی هر فریم ---- */
  update(dt, t, playing) {
    /* اگر متصل نیست یا پخش نمی‌شود، خاموشی سریع */
    if (!this.connected || !playing) {
      this.rms     *= 0.55;
      this.bass    *= 0.55;
      this.mid     *= 0.55;
      this.high    *= 0.55;
      this.vocal   *= 0.55;
      this.flux    *= 0.55;
      this.sBass    = smooth(this.sBass, 0, 6, dt);
      this.sMid     = smooth(this.sMid, 0, 6, dt);
      this.sHigh    = smooth(this.sHigh, 0, 6, dt);
      this.sEnergy  = smooth(this.sEnergy, 0, 5, dt);
      this.sVocal   = smooth(this.sVocal, 0, 6, dt);
      this.pulse   *= 0.8;
      this.silence = Math.min(1, this.silence + dt * 6);
      return;
    }

    this.analyser.getByteFrequencyData(this.freq);
    this.analyser.getFloatTimeDomainData(this.time);

    /* --- RMS (دامنه‌ی کل) --- */
    let sum = 0;
    for (let i = 0; i < this.time.length; i++) sum += this.time[i] * this.time[i];
    const rms = Math.sqrt(sum / this.time.length);

    /* --- باندها --- */
    const bass = this.bandAvg(1, 8);
    const mid  = this.bandAvg(8, 90);
    const high = this.bandAvg(90, 400);

    /* --- باند وکال: ۳۰۰ تا ۳۴۰۰ هرتز --- */
    const binHz = this.ctx.sampleRate / this.analyser.fftSize;
    const vFrom = Math.max(1, Math.floor(300 / binHz));
    const vTo   = Math.min(this.freq.length - 1, Math.floor(3400 / binHz));
    let vSum = 0, vCount = 0;
    for (let i = vFrom; i < vTo; i++) { vSum += this.freq[i]; vCount++; }
    const vocalRaw = vCount ? vSum / (vCount * 255) : 0;

    /* --- flux طیفی (نرخ تغییر) --- */
    let flux = 0;
    for (let i = 1; i < 250; i++) {
      const d = this.freq[i] / 255 - this.prevFreq[i];
      if (d > 0) flux += d;
    }
    flux /= 250;
    for (let i = 0; i < this.freq.length; i++) this.prevFreq[i] = this.freq[i] / 255;

    /* --- گیت سکوت پویا نسبت به میانگین ۳ ثانیه‌ی اخیر --- */
    this.history.push(rms);
    if (this.history.length > 90) this.history.shift();
    const avgHist = this.history.reduce((a, b) => a + b, 0) / this.history.length;

    const silent =
      rms < 0.012 ||
      (avgHist > 0.02 && rms < avgHist * 0.32 && flux < 0.006);

    /* --- تشخیص وکال ---
       وکال یعنی:
         • انرژی در باند میانی-بالا (۳۰۰–۳۴۰۰)
         • bass غالب نباشد (کیک و بیس ضربه‌ای وکال نیست)
       */
    const bassDominance = bass / (mid + high + 0.02);
    const bassGate = clamp(1.6 - bassDominance);
    const vocalPresence = clamp((vocalRaw - 0.05) / 0.20) * bassGate;

    /* --- ذخیره‌ی آنی --- */
    this.rms      = rms;
    this.bass     = bass;
    this.mid      = mid;
    this.high     = high;
    this.vocalRaw = vocalRaw;
    this.vocal    = vocalPresence * (silent ? 0 : 1);
    this.flux     = flux;
    this.silence  = silent
      ? Math.min(1, this.silence + dt * 9)   // ورود سریع به سکوت
      : Math.max(0, this.silence - dt * 14); // خروج سریع از سکوت

    /* --- نرم‌سازی با attack/release جداگانه --- */
    this.sBass  = smoothAR(this.sBass,  bass,  12, 4, dt);
    this.sMid   = smoothAR(this.sMid,   mid,   12, 4, dt);
    this.sHigh  = smoothAR(this.sHigh,  high,  14, 4, dt);
    this.sVocal = smoothAR(this.sVocal, this.vocal, 22, 8, dt);

    const energy = clamp((bass * 0.4 + mid * 0.4 + high * 0.2 - 0.12) / 0.5);
    this.sEnergy = smoothAR(this.sEnergy, energy * (1 - this.silence), 10, 3, dt);

    /* --- onset و پالس --- */
    this.pulse *= Math.exp(-dt * 11);   // افت سریع (~۹۰ms)
    if (!silent && flux > 0.010 && t - this.lastOnset > 0.20) {
      if (bass > 0.30) {
        const err = Math.round(this.beat) - this.beat;
        this.beat += err * 0.35;
      }
      this.lastOnset = t;
      this.onsets.push(t);
      if (this.onsets.length > 64) this.onsets.shift();
      this.pulse = clamp(0.4 + flux * 8);
      this.estimateBpm();
    }
    this.beat += dt * this.bpm / 60;
  }

  /* تخمین BPM از فاصله‌ی onsetها */
  estimateBpm() {
    const on = this.onsets;
    if (on.length < 8) return;
    const hist = new Float32Array(60);
    for (let i = 1; i < on.length; i++) {
      for (let j = 1; j <= 3 && i - j >= 0; j++) {
        const d = on[i] - on[i - j];
        if (d < 0.18 || d > 2.5) continue;
        let b = 60 / d;
        while (b < 70) b *= 2;
        while (b > 180) b /= 2;
        const idx = Math.round((b - 70) / 2);
        if (idx >= 0 && idx < 60) {
          hist[idx] += 1 / j;
          if (idx > 0)  hist[idx - 1] += 0.4 / j;
          if (idx < 59) hist[idx + 1] += 0.4 / j;
        }
      }
    }
    let bi = 0;
    for (let i = 1; i < 60; i++) if (hist[i] > hist[bi]) bi = i;
    if (hist[bi] < 1.5) return;
    const newBpm = 70 + bi * 2;
    this.bpm = lerp(this.bpm, newBpm, 0.22);
    this.hasBpm = true;
  }

  /* ریست کامل (هنگام لود آهنگ جدید) */
  reset() {
    this.onsets.length = 0;
    this.history.length = 0;
    this.hasBpm = false;
    this.bpm = 100;
    this.beat = 0;
    this.silence = 1;
    this.pulse = 0;
    this.vocal = 0;
    this.sVocal = 0;
    this.sEnergy = 0;
  }
}


/* ============================================================================
   ۲) سیستم سبک‌ها
   ----------------------------------------------------------------------------
   هر سبک: پالت رنگ، لباس، ساز گیتار، آیا پیانو دارد، آیکن کارت.
   ============================================================================ */

const STYLES = {
  rock: {
    name: 'راک',
    tagline: 'چرم، دیستورشن، شور',
    accent: '#ff3a20',
    swatch: '#151515',
    guitar: 'electric',
    hasPiano: false,
    hasAmp: true,
    clothes: { type: 'leather', color: '#181818', accent: '#a0a0a0', accessory: 'studs' },
    effects: { shake: 1.0, headbang: 1.0, particles: 'sparks' },
    icon: `<svg viewBox="0 0 64 64">
      <ellipse cx="28" cy="42" rx="14" ry="12" fill="#181818" stroke="#000" stroke-width="2"/>
      <circle cx="28" cy="42" r="4" fill="#8a8a8a"/>
      <line x1="38" y1="34" x2="46" y2="14" stroke="#8a8a8a" stroke-width="3" stroke-linecap="round"/>
    </svg>`
  },
  pop: {
    name: 'پاپ',
    tagline: 'رنگ، شادی، پرش',
    accent: '#ff5aa8',
    swatch: '#ff7cb0',
    guitar: 'acoustic',
    hasPiano: true,
    hasAmp: false,
    clothes: { type: 'tshirt', color: '#ff7cb0', accent: '#fff', accessory: 'headband' },
    effects: { shake: 0.4, headbang: 0.3, particles: 'confetti' },
    icon: `<svg viewBox="0 0 64 64">
      <circle cx="32" cy="32" r="20" fill="#ff7cb0" stroke="#000" stroke-width="2"/>
      <path d="M22 28 Q32 20 42 28" stroke="#fff" stroke-width="2" fill="none"/>
      <circle cx="26" cy="34" r="2" fill="#1c1410"/>
      <circle cx="38" cy="34" r="2" fill="#1c1410"/>
    </svg>`
  },
  classic: {
    name: 'کلاسیک',
    tagline: 'وقار، ساز چوبی',
    accent: '#c9a961',
    swatch: '#2a1d12',
    guitar: 'classical',
    hasPiano: true,
    hasAmp: false,
    clothes: { type: 'tuxedo', color: '#1c1c1c', accent: '#fff', accessory: 'bowtie' },
    effects: { shake: 0.12, headbang: 0.1, particles: 'notes' },
    icon: `<svg viewBox="0 0 64 64">
      <ellipse cx="32" cy="42" rx="12" ry="11" fill="#c9a961" stroke="#000" stroke-width="2"/>
      <circle cx="32" cy="42" r="3" fill="#4a3010"/>
      <path d="M26 14l6 4v10" stroke="#8a6a30" stroke-width="3" fill="none"/>
    </svg>`
  },
  jazz: {
    name: 'جاز',
    tagline: 'دود، کلاه، شب',
    accent: '#ffb04a',
    swatch: '#2a2438',
    guitar: 'jazz',
    hasPiano: true,
    hasAmp: false,
    clothes: { type: 'suit', color: '#2a2438', accent: '#c9a961', accessory: 'fedora' },
    effects: { shake: 0.3, headbang: 0.3, particles: 'smoke' },
    icon: `<svg viewBox="0 0 64 64">
      <path d="M14 30h36v4H14z" fill="#2a2438"/>
      <path d="M20 22h24v8H20z" fill="#3a3248"/>
      <ellipse cx="32" cy="46" rx="10" ry="8" fill="#ffb04a" stroke="#000" stroke-width="2"/>
    </svg>`
  },
  electronic: {
    name: 'الکترونیک',
    tagline: 'نئون، پالس، بیت',
    accent: '#20e0ff',
    swatch: '#0a0520',
    guitar: 'synth',
    hasPiano: false,
    hasAmp: false,
    clothes: { type: 'neon', color: '#0a1030', accent: '#20e0ff', accessory: 'headset' },
    effects: { shake: 0.6, headbang: 0.5, particles: 'neon' },
    icon: `<svg viewBox="0 0 64 64">
      <rect x="10" y="20" width="44" height="24" rx="3" fill="#0a1030" stroke="#20e0ff" stroke-width="2"/>
      <path d="M18 32 L24 24 L28 40 L34 22 L38 42 L44 30 L48 34"
            stroke="#20e0ff" stroke-width="2" fill="none"/>
    </svg>`
  },
  hiphop: {
    name: 'هیپ‌هاپ',
    tagline: 'گشاد، طلایی، بیس',
    accent: '#ffcc20',
    swatch: '#202020',
    guitar: null,
    hasPiano: false,
    hasAmp: false,
    clothes: { type: 'hoodie', color: '#202020', accent: '#ffcc20', accessory: 'chain' },
    effects: { shake: 0.5, headbang: 0.6, particles: 'gold' },
    icon: `<svg viewBox="0 0 64 64">
      <circle cx="32" cy="30" r="14" fill="#202020" stroke="#ffcc20" stroke-width="2"/>
      <circle cx="32" cy="30" r="4" fill="#ffcc20"/>
      <path d="M20 46h24" stroke="#ffcc20" stroke-width="3" stroke-linecap="round"/>
    </svg>`
  }
};


/* ============================================================================
   ۳) سیستم ذرات
   ============================================================================ */

class Particles {
  constructor() {
    this.items = [];
  }

  /** ایجاد یک دسته‌ی ذره در موقعیت مشخص */
  spawn(type, x, y, hue) {
    const CONF = {
      sparks:   { n: 6, life: [.3, .6], vx: 3, vy: -4, g: 12, size: [1, 2],
                  color: () => `hsl(${20 + Math.random() * 30} 95% 60%)` },
      confetti: { n: 8, life: [.8, 1.4], vx: 4, vy: -5, g: 10, size: [2, 4],
                  color: () => `hsl(${Math.random() * 360} 80% 65%)` },
      notes:    { n: 4, life: [.9, 1.5], vx: 2, vy: -3, g: 2, size: [10, 14],
                  color: () => `hsl(${hue || 40} 70% 78%)`, glyph: true },
      smoke:    { n: 4, life: [1.2, 2.0], vx: 2, vy: -1.5, g: 0, size: [4, 8],
                  color: () => `hsla(30, 40%, 70%, .5)` },
      neon:     { n: 6, life: [.5, .9], vx: 5, vy: -2, g: 6, size: [1.5, 3],
                  color: () => `hsl(${190 + Math.random() * 40} 95% 65%)` },
      gold:     { n: 5, life: [.6, 1.0], vx: 3, vy: -3, g: 8, size: [2, 3],
                  color: () => `hsl(45 95% 60%)` }
    }[type];
    if (!CONF) return;

    for (let i = 0; i < CONF.n; i++) {
      this.items.push({
        x, y,
        vx: rand(-CONF.vx, CONF.vx),
        vy: rand(CONF.vy * 0.5, CONF.vy * 1.2),
        g: CONF.g,
        life: rand(CONF.life[0], CONF.life[1]),
        maxLife: CONF.life[1],
        size: rand(CONF.size[0], CONF.size[1]),
        color: CONF.color(),
        glyph: !!CONF.glyph
      });
    }
    if (this.items.length > 400) this.items.splice(0, this.items.length - 400);
  }

  update(dt) {
    for (let i = this.items.length - 1; i >= 0; i--) {
      const p = this.items[i];
      p.life -= dt;
      if (p.life <= 0) { this.items.splice(i, 1); continue; }
      p.vy += p.g * dt;
      p.x  += p.vx * dt;
      p.y  += p.vy * dt;
    }
  }

  draw(g) {
    for (const p of this.items) {
      const a = clamp(p.life / p.maxLife);
      g.globalAlpha = a;
      if (p.glyph) {
        g.fillStyle = p.color;
        g.font = `${p.size * 2}px serif`;
        g.fillText('♪', p.x, p.y);
      } else {
        g.fillStyle = p.color;
        g.beginPath();
        g.arc(p.x, p.y, p.size, 0, 7);
        g.fill();
      }
    }
    g.globalAlpha = 1;
  }
}


/* ============================================================================
   ۴) تعریف گربه‌ها
   ----------------------------------------------------------------------------
   هر گربه: نقش، رنگ، و پارامترهای اختصاصی اسکلت.
   ============================================================================ */

const CAT_DEFS = [
  {
    key: 'orange', role: 'guitar', roleName: 'گیتار',
    colors: { body: '#e8923a', belly: '#fbe2bd', dark: '#b8651f' },
    cfg: { bodyW: 0.66, bodyH: 1.05, headR: 0.24, legLen: 0.30,
           earType: 'point', tailType: 'long', pattern: 'tabby', mult: 1.0 }
  },
  {
    key: 'tux', role: 'drums', roleName: 'درام',
    colors: { body: '#1d1d26', belly: '#f6f6f4', dark: '#000' },
    cfg: { bodyW: 0.60, bodyH: 1.15, headR: 0.22, legLen: 0.28,
           earType: 'point', tailType: 'whip', pattern: 'tux', mult: 1.5 }
  },
  {
    key: 'crown', role: 'vocal', roleName: 'خواننده',
    colors: { body: '#fdfbf8', belly: '#ffe9ee', dark: '#cfc6c0' },
    cfg: { bodyW: 0.50, bodyH: 0.92, headR: 0.27, legLen: 0.30,
           earType: 'point', tailType: 'curl', pattern: 'none', mult: 1.0 }
  },
  {
    key: 'mint', role: 'keys', roleName: 'کیبورد',
    colors: { body: '#e9c8a0', belly: '#f9ecd8', dark: '#c49a6c' },
    cfg: { bodyW: 0.60, bodyH: 0.92, headR: 0.25, legLen: 0.28,
           earType: 'fold', tailType: 'stub', pattern: 'none', mult: 0.75 }
  },
  {
    key: 'calico', role: 'bass', roleName: 'بیس',
    colors: { body: '#f3ece3', belly: '#fff', dark: '#6b4a38' },
    cfg: { bodyW: 0.54, bodyH: 0.82, headR: 0.26, legLen: 0.28,
           earType: 'point', tailType: 'long', pattern: 'calico', mult: 0.5 }
  }
];


/* ============================================================================
   ۵) توابع کمکی رسم
   ----------------------------------------------------------------------------
   همه‌ی این توابع فرض می‌کنند گربه در مبدأ (۰،۰) = زمین ایستاده،
   و Y منفی به سمت بالا است.
   ============================================================================ */

/* --- IK دو بندی برای دست ---
   با زاویه‌ی شانه a1 و زاویه‌ی نسبی آرنج a2، موقعیت دست محاسبه می‌شود. */
function solveArm(sx, sy, a1, a2, upper, fore) {
  const ex = sx + Math.cos(a1) * upper;
  const ey = sy + Math.sin(a1) * upper;
  const hx = ex + Math.cos(a1 + a2) * fore;
  const hy = ey + Math.sin(a1 + a2) * fore;
  return { sx, sy, ex, ey, hx, hy };
}

/* --- پا --- */
function drawLeg(g, cat, hipX, hipY, side) {
  const col = cat.colors;
  const footX = hipX + side * 0.06;
  const footY = 0;
  // زانو کمی به بیرون می‌شکند
  const kx = lerp(hipX, footX, 0.5) + (footX - hipX) * 0.15;
  const ky = lerp(hipY, footY, 0.5);

  g.strokeStyle = col.body;
  g.lineWidth = 0.14;
  g.lineCap = 'round';
  g.beginPath();
  g.moveTo(hipX, hipY);
  g.quadraticCurveTo(kx, ky, footX, footY - 0.02);
  g.stroke();

  // کف پا
  g.fillStyle = col.belly;
  g.beginPath();
  g.ellipse(footX, footY - 0.035, 0.09, 0.05, 0, 0, 7);
  g.fill();
}

/* --- دنباله --- */
function drawTail(g, cat, tx, ty) {
  const col = cat.colors;
  const c = cat.cfg;
  let x = tx, y = ty;
  let a = -0.5;
  g.strokeStyle = col.body;
  g.lineCap = 'round';
  g.lineWidth = c.tailType === 'stub' ? 0.16 : 0.10;

  g.beginPath();
  g.moveTo(x, y);

  const N = c.tailType === 'stub' ? 1 : 3;
  for (let i = 0; i < N; i++) {
    const len = c.tailType === 'stub' ? 0.18 : 0.22 - i * 0.02;
    a += (cat.tailSegs[i] || 0) * 0.7;
    x += Math.cos(a) * len;
    y += Math.sin(a) * len;
    g.lineTo(x, y);
  }
  g.stroke();
}

/* --- دست --- */
function drawArm(g, cat, arm) {
  const col = cat.colors;
  g.strokeStyle = col.body;
  g.lineWidth = 0.10;
  g.lineCap = 'round';
  g.beginPath();
  g.moveTo(arm.sx, arm.sy);
  g.lineTo(arm.ex, arm.ey);
  g.lineTo(arm.hx, arm.hy);
  g.stroke();

  g.fillStyle = col.belly;
  g.beginPath();
  g.arc(arm.hx, arm.hy, 0.06, 0, 7);
  g.fill();
}

/* --- الگوی خز روی بدن --- */
function drawPattern(g, cat, bodyW, bodyH) {
  const col = cat.colors;
  const p = cat.cfg.pattern;

  if (p === 'tabby') {
    g.strokeStyle = col.dark;
    g.lineWidth = 0.028;
    for (let i = -1; i <= 1; i++) {
      g.beginPath();
      g.moveTo(-bodyW * 0.5 + 0.02, -bodyH * 0.5 + i * 0.14);
      g.quadraticCurveTo(-bodyW * 0.35, -bodyH * 0.46 + i * 0.14,
                         -bodyW * 0.22, -bodyH * 0.5 + i * 0.14);
      g.stroke();
    }
  } else if (p === 'calico') {
    g.fillStyle = col.dark;
    g.beginPath();
    g.ellipse(-bodyW * 0.25, -bodyH * 0.1, 0.10, 0.09, 0, 0, 7);
    g.fill();
    g.fillStyle = '#d98e4a';
    g.beginPath();
    g.ellipse(bodyW * 0.28, bodyH * 0.1, 0.09, 0.08, 0, 0, 7);
    g.fill();
  }
}

/* --- لباس بر اساس سبک --- */
function drawClothes(g, cat, style, bodyW, bodyH) {
  const cl = style.clothes;
  if (!cl) return;

  if (cl.type === 'leather') {
    g.fillStyle = cl.color;
    g.beginPath();
    g.ellipse(0, bodyH * 0.05, bodyW * 0.5, bodyH * 0.4, 0, 0, 7);
    g.fill();
    // یقه
    g.fillStyle = '#2a2a2a';
    g.beginPath();
    g.moveTo(-bodyW * 0.3, -bodyH * 0.3);
    g.lineTo(0, -bodyH * 0.15);
    g.lineTo(bodyW * 0.3, -bodyH * 0.3);
    g.lineTo(bodyW * 0.15, -bodyH * 0.35);
    g.lineTo(0, -bodyH * 0.22);
    g.lineTo(-bodyW * 0.15, -bodyH * 0.35);
    g.closePath();
    g.fill();
    // میخ‌های فلزی
    g.fillStyle = cl.accent;
    for (let i = -1; i <= 1; i++) {
      g.beginPath();
      g.arc(i * bodyW * 0.18, bodyH * 0.28, 0.015, 0, 7);
      g.fill();
    }
    // شلوار جین
    g.fillStyle = '#3b4a66';
    g.beginPath();
    g.ellipse(0, bodyH * 0.35, bodyW * 0.42, bodyH * 0.12, 0, 0, 7);
    g.fill();
  } else if (cl.type === 'tshirt') {
    g.fillStyle = cl.color;
    g.beginPath();
    g.ellipse(0, bodyH * 0.08, bodyW * 0.46, bodyH * 0.36, 0, 0, 7);
    g.fill();
    g.strokeStyle = cl.accent;
    g.lineWidth = 0.03;
    g.beginPath();
    g.arc(0, -bodyH * 0.22, bodyW * 0.2, 0.15 * Math.PI, 0.85 * Math.PI);
    g.stroke();
  } else if (cl.type === 'tuxedo') {
    g.fillStyle = cl.color;
    g.beginPath();
    g.ellipse(0, bodyH * 0.08, bodyW * 0.46, bodyH * 0.4, 0, 0, 7);
    g.fill();
    // پیراهن
    g.fillStyle = cl.accent;
    g.beginPath();
    g.moveTo(-bodyW * 0.18, -bodyH * 0.3);
    g.lineTo(bodyW * 0.18, -bodyH * 0.3);
    g.lineTo(bodyW * 0.14, bodyH * 0.3);
    g.lineTo(-bodyW * 0.14, bodyH * 0.3);
    g.closePath();
    g.fill();
    // پاپیون
    g.fillStyle = '#000';
    const by = -bodyH * 0.28;
    g.beginPath();
    g.moveTo(0, by); g.lineTo(-0.05, by - 0.03); g.lineTo(-0.05, by + 0.03);
    g.closePath();
    g.fill();
    g.beginPath();
    g.moveTo(0, by); g.lineTo(0.05, by - 0.03); g.lineTo(0.05, by + 0.03);
    g.closePath();
    g.fill();
  } else if (cl.type === 'suit') {
    g.fillStyle = cl.color;
    g.beginPath();
    g.ellipse(0, bodyH * 0.08, bodyW * 0.48, bodyH * 0.4, 0, 0, 7);
    g.fill();
    g.strokeStyle = cl.accent;
    g.lineWidth = 0.02;
    g.beginPath();
    g.moveTo(-bodyW * 0.2, -bodyH * 0.28);
    g.lineTo(0, -bodyH * 0.05);
    g.lineTo(bodyW * 0.2, -bodyH * 0.28);
    g.stroke();
  } else if (cl.type === 'neon') {
    g.fillStyle = cl.color;
    g.beginPath();
    g.ellipse(0, bodyH * 0.08, bodyW * 0.46, bodyH * 0.36, 0, 0, 7);
    g.fill();
    g.strokeStyle = cl.accent;
    g.lineWidth = 0.025;
    for (let i = -1; i <= 1; i++) {
      g.beginPath();
      g.moveTo(-bodyW * 0.4, bodyH * 0.05 + i * 0.12);
      g.lineTo(bodyW * 0.4, bodyH * 0.05 + i * 0.12);
      g.stroke();
    }
  } else if (cl.type === 'hoodie') {
    g.fillStyle = cl.color;
    g.beginPath();
    g.ellipse(0, bodyH * 0.1, bodyW * 0.5, bodyH * 0.4, 0, 0, 7);
    g.fill();
    // زنجیر طلایی
    g.strokeStyle = cl.accent;
    g.lineWidth = 0.025;
    g.beginPath();
    g.arc(0, -bodyH * 0.05, bodyW * 0.25, 0.15 * Math.PI, 0.85 * Math.PI);
    g.stroke();
    g.fillStyle = cl.accent;
    g.beginPath();
    g.arc(0, bodyH * 0.15, 0.03, 0, 7);
    g.fill();
  }
}

/* --- ساز گیتار (همه‌ی انواع) --- */
function drawGuitar(g, kind, armL, armR) {
  const handL = { x: armL.hx, y: armL.hy };
  const handR = { x: armR.hx, y: armR.hy };
  const cx = handL.x * 0.35 + handR.x * 0.65;
  const cy = handL.y * 0.35 + handR.y * 0.65 + 0.08;
  const ang = Math.atan2(handR.y - handL.y, handR.x - handL.x);

  g.save();
  g.translate(cx, cy);
  g.rotate(ang * 0.7);

  if (kind === 'electric') {
    g.fillStyle = '#1a1a1a';
    g.strokeStyle = '#000';
    g.lineWidth = 0.015;
    g.beginPath();
    g.moveTo(-0.15, 0.02);
    g.bezierCurveTo(-0.18, -0.08, -0.05, -0.14, 0.02, -0.12);
    g.bezierCurveTo(0.08, -0.14, 0.20, -0.08, 0.20, 0.02);
    g.bezierCurveTo(0.22, 0.08, 0.08, 0.14, 0, 0.12);
    g.bezierCurveTo(-0.08, 0.14, -0.18, 0.08, -0.15, 0.02);
    g.closePath();
    g.fill();
    g.stroke();
    // پیکاپ
    g.fillStyle = '#c8c8c8';
    g.fillRect(-0.05, -0.02, 0.04, 0.04);
    g.fillRect(0.00, -0.02, 0.04, 0.04);
    // دسته
    g.fillStyle = '#3a2a1f';
    g.fillRect(0.17, -0.02, 0.40, 0.04);
    g.strokeStyle = '#e0d0a0';
    g.lineWidth = 0.005;
    for (let i = 0; i < 6; i++) {
      g.beginPath();
      g.moveTo(0.20 + i * 0.06, -0.02);
      g.lineTo(0.20 + i * 0.06, 0.02);
      g.stroke();
    }
  } else if (kind === 'acoustic') {
    g.fillStyle = '#d9a86a';
    g.strokeStyle = '#5a3a1a';
    g.lineWidth = 0.012;
    g.beginPath();
    g.ellipse(0, 0, 0.16, 0.12, 0, 0, 7);
    g.fill(); g.stroke();
    g.fillStyle = '#2a1a10';
    g.beginPath(); g.arc(0.01, 0, 0.03, 0, 7); g.fill();
    g.fillStyle = '#7a5a3a';
    g.fillRect(0.15, -0.02, 0.42, 0.04);
    g.strokeStyle = '#e0d0a0';
    g.lineWidth = 0.005;
    for (let i = 0; i < 6; i++) {
      g.beginPath();
      g.moveTo(0.20 + i * 0.06, -0.02);
      g.lineTo(0.20 + i * 0.06, 0.02);
      g.stroke();
    }
  } else if (kind === 'classical') {
    g.fillStyle = '#e0b878';
    g.strokeStyle = '#6a4a20';
    g.lineWidth = 0.012;
    g.beginPath();
    g.ellipse(0, 0, 0.17, 0.13, 0, 0, 7);
    g.fill(); g.stroke();
    g.fillStyle = '#2a1a10';
    g.beginPath(); g.arc(0.01, 0, 0.032, 0, 7); g.fill();
    g.fillStyle = '#5a3a1a';
    g.fillRect(0.16, -0.02, 0.42, 0.04);
  } else if (kind === 'jazz') {
    g.fillStyle = '#8a4a1a';
    g.strokeStyle = '#3a2010';
    g.lineWidth = 0.012;
    g.beginPath();
    g.ellipse(0, 0, 0.17, 0.13, 0, 0, 7);
    g.fill(); g.stroke();
    // f-hole
    g.strokeStyle = '#000';
    g.lineWidth = 0.008;
    g.beginPath();
    g.moveTo(-0.08, -0.04); g.quadraticCurveTo(-0.06, 0, -0.08, 0.04);
    g.stroke();
    g.beginPath();
    g.moveTo(0.08, -0.04); g.quadraticCurveTo(0.06, 0, 0.08, 0.04);
    g.stroke();
    g.fillStyle = '#3a2a1a';
    g.fillRect(0.16, -0.02, 0.42, 0.04);
  } else if (kind === 'bass') {
    g.fillStyle = '#1a1a1a';
    g.strokeStyle = '#000';
    g.lineWidth = 0.015;
    g.beginPath();
    g.moveTo(-0.16, 0.02);
    g.bezierCurveTo(-0.20, -0.10, -0.05, -0.15, 0.02, -0.13);
    g.bezierCurveTo(0.10, -0.15, 0.22, -0.10, 0.22, 0.02);
    g.bezierCurveTo(0.24, 0.09, 0.08, 0.14, 0, 0.12);
    g.bezierCurveTo(-0.08, 0.14, -0.20, 0.09, -0.16, 0.02);
    g.closePath();
    g.fill(); g.stroke();
    g.fillStyle = '#c8c8c8';
    g.fillRect(-0.05, -0.02, 0.05, 0.04);
    g.fillRect(0.01, -0.02, 0.05, 0.04);
    g.fillStyle = '#3a2a1f';
    g.fillRect(0.19, -0.025, 0.45, 0.05);
    g.strokeStyle = '#e0d0a0';
    g.lineWidth = 0.005;
    for (let i = 0; i < 5; i++) {
      g.beginPath();
      g.moveTo(0.22 + i * 0.08, -0.025);
      g.lineTo(0.22 + i * 0.08, 0.025);
      g.stroke();
    }
  } else if (kind === 'synth') {
    g.fillStyle = '#1a1030';
    g.strokeStyle = '#20e0ff';
    g.lineWidth = 0.015;
    g.beginPath();
    g.ellipse(0, 0, 0.18, 0.10, 0, 0, 7);
    g.fill(); g.stroke();
    g.fillStyle = '#20e0ff';
    for (let i = 0; i < 8; i++) {
      g.fillRect(-0.15 + i * 0.038, -0.03, 0.02, 0.06);
    }
  }
  g.restore();
}

/* --- کیت درام --- */
function drawDrumKit(g, cat, bodyW, bodyH) {
  g.save();
  g.translate(0, -0.05);

  // بیس درام
  g.fillStyle = '#8a2a20';
  g.strokeStyle = '#000';
  g.lineWidth = 0.02;
  g.beginPath();
  g.arc(0, -0.08, 0.14, 0, 7);
  g.fill(); g.stroke();
  g.fillStyle = '#fff5d8';
  g.beginPath();
  g.arc(0, -0.08, 0.05, 0, 7);
  g.fill();

  // توم چپ
  g.fillStyle = '#c88a3a';
  g.beginPath();
  g.ellipse(-0.18, -0.22, 0.09, 0.05, 0, 0, 7);
  g.fill(); g.stroke();

  // توم راست
  g.beginPath();
  g.ellipse(0.05, -0.24, 0.09, 0.05, 0, 0, 7);
  g.fill(); g.stroke();

  // های‌هت
  g.fillStyle = '#c8a860';
  g.beginPath();
  g.ellipse(-0.32, -0.32, 0.06, 0.02, 0, 0, 7);
  g.fill(); g.stroke();

  // سنج
  g.fillStyle = '#e0c060';
  g.beginPath();
  g.ellipse(0.30, -0.36, 0.09, 0.02, 0, 0, 7);
  g.fill(); g.stroke();

  g.restore();
}

/* --- میکروفون --- */
function drawMic(g, armL) {
  const hx = armL.hx, hy = armL.hy;
  g.save();
  g.translate(hx, hy - 0.06);
  g.rotate(-0.4);

  g.fillStyle = '#333';
  g.strokeStyle = '#000';
  g.lineWidth = 0.012;
  g.beginPath();
  g.roundRect(-0.03, -0.14, 0.06, 0.16, 0.02);
  g.fill(); g.stroke();

  g.fillStyle = '#888';
  g.beginPath();
  g.ellipse(0, -0.16, 0.045, 0.04, 0, 0, 7);
  g.fill(); g.stroke();

  g.strokeStyle = '#aaa';
  g.lineWidth = 0.005;
  for (let i = 0; i < 4; i++) {
    g.beginPath();
    g.moveTo(-0.04, -0.17 + i * 0.01);
    g.lineTo(0.04, -0.17 + i * 0.01);
    g.stroke();
  }
  g.restore();
}

/* --- کیبورد --- */
function drawKeyboard(g, cat, bodyW, style) {
  const isElectronic = style === 'electronic';
  g.save();
  g.translate(0, -0.05);

  // بدنه
  g.fillStyle = isElectronic ? '#0a1030' : '#2a1a10';
  g.strokeStyle = isElectronic ? '#20e0ff' : '#000';
  g.lineWidth = 0.015;
  g.beginPath();
  g.roundRect(-bodyW * 0.6, -0.12, bodyW * 1.2, 0.14, 0.02);
  g.fill(); g.stroke();

  // کلیدهای سفید
  g.fillStyle = isElectronic ? '#d0f0ff' : '#f1e4cc';
  const N = 12;
  for (let i = 0; i < N; i++) {
    g.fillRect(
      -bodyW * 0.55 + i * (bodyW * 1.1 / N),
      -0.10,
      (bodyW * 1.1 / N) - 0.006,
      0.10
    );
  }
  // کلیدهای سیاه
  g.fillStyle = '#000';
  for (let i = 0; i < N; i++) {
    if (i % 7 === 2 || i % 7 === 6) continue;
    if (i % 2 === 1) {
      g.fillRect(
        -bodyW * 0.55 + i * (bodyW * 1.1 / N) + 0.008,
        -0.10,
        (bodyW * 1.1 / N) * 0.55,
        0.06
      );
    }
  }
  g.restore();
}

/* --- آمپ گیتار --- */
function drawAmp(g, bodyW) {
  g.save();
  g.translate(bodyW * 0.7, -0.10);

  g.fillStyle = '#151515';
  g.strokeStyle = '#000';
  g.lineWidth = 0.015;
  g.beginPath();
  g.roundRect(-0.14, -0.20, 0.28, 0.24, 0.02);
  g.fill(); g.stroke();

  g.fillStyle = '#3a3a3a';
  g.beginPath();
  g.roundRect(-0.12, -0.18, 0.24, 0.16, 0.01);
  g.fill();

  g.strokeStyle = '#666';
  g.lineWidth = 0.004;
  for (let i = 0; i < 8; i++) {
    g.beginPath();
    g.moveTo(-0.12, -0.17 + i * 0.02);
    g.lineTo(0.12, -0.17 + i * 0.02);
    g.stroke();
  }

  // ولوم
  g.fillStyle = '#c9a961';
  g.beginPath();
  g.arc(0.06, -0.02, 0.015, 0, 7);
  g.fill();
  g.restore();
}

/* --- سر گربه --- */
function drawHead(g, cat, style, t) {
  const col = cat.colors;
  const r = cat.cfg.headR;
  const asleep = cat.eyeShut > 0.7;

  /* گوش‌ها */
  g.fillStyle = col.body;
  for (let s = -1; s <= 1; s += 2) {
    g.save();
    g.translate(s * r * 0.65, -r * 0.7);
    g.rotate(s * (0.1 + (s < 0 ? cat.earL : cat.earR)));
    if (cat.cfg.earType === 'point') {
      g.beginPath();
      g.moveTo(-r * 0.3, r * 0.4);
      g.lineTo(0, -r * 0.65);
      g.lineTo(r * 0.3, r * 0.4);
      g.closePath();
      g.fill();
      // داخل گوش
      g.fillStyle = '#f2a3a8';
      g.beginPath();
      g.moveTo(-r * 0.16, r * 0.28);
      g.lineTo(0, -r * 0.42);
      g.lineTo(r * 0.16, r * 0.28);
      g.closePath();
      g.fill();
      g.fillStyle = col.body;
    } else {
      // گوش تاشو
      g.beginPath();
      g.ellipse(0, 0, r * 0.28, r * 0.22, 0, 0, 7);
      g.fill();
    }
    g.restore();
  }

  /* سر */
  g.fillStyle = col.body;
  g.beginPath();
  g.ellipse(0, 0, r * 1.12, r, 0, 0, 7);
  g.fill();

  /* پوزه */
  g.fillStyle = col.belly;
  g.beginPath();
  g.ellipse(0, r * 0.35, r * 0.55, r * 0.42, 0, 0, 7);
  g.fill();

  /* الگوهای صورت */
  if (cat.cfg.pattern === 'tux') {
    g.fillStyle = '#f6f6f4';
    g.beginPath();
    g.moveTo(0, -r * 0.9);
    g.lineTo(-r * 0.14, r * 0.1);
    g.lineTo(r * 0.14, r * 0.1);
    g.closePath();
    g.fill();
  } else if (cat.cfg.pattern === 'calico') {
    g.fillStyle = col.dark;
    g.beginPath();
    g.ellipse(-r * 0.6, -r * 0.3, r * 0.45, r * 0.4, 0, 0, 7);
    g.fill();
    g.fillStyle = '#d98e4a';
    g.beginPath();
    g.ellipse(r * 0.6, -r * 0.5, r * 0.32, r * 0.28, 0, 0, 7);
    g.fill();
  } else if (cat.cfg.pattern === 'tabby') {
    g.strokeStyle = col.dark;
    g.lineWidth = 0.02;
    for (const x of [-0.05, 0, 0.05]) {
      g.beginPath();
      g.moveTo(x, -r * 0.9);
      g.lineTo(x, -r * 0.55);
      g.stroke();
    }
  }

  /* چشم‌ها */
  const blink = cat.blinkT > 3.9 && cat.blinkT < 4.05;
  const eyeY = -r * 0.05;
  const eyeR = r * 0.17;
  for (let s = -1; s <= 1; s += 2) {
    const ex = s * r * 0.42;
    if (asleep || blink) {
      g.strokeStyle = '#1c1410';
      g.lineWidth = 0.02;
      g.beginPath();
      g.arc(ex, eyeY, eyeR, 0.15, Math.PI - 0.15);
      g.stroke();
    } else {
      g.fillStyle = '#fff';
      g.beginPath();
      g.ellipse(ex, eyeY, eyeR, eyeR * 1.15, 0, 0, 7);
      g.fill();
      g.fillStyle = cat.cfg.pattern === 'tux' ? '#9be15d' : '#1c1410';
      g.beginPath();
      g.ellipse(ex, eyeY, eyeR * 0.55, eyeR * 0.95, 0, 0, 7);
      g.fill();
      g.fillStyle = '#fff';
      g.beginPath();
      g.arc(ex + r * 0.04, eyeY - r * 0.05, r * 0.05, 0, 7);
      g.fill();
    }
  }

  /* بینی */
  g.fillStyle = '#f27c8c';
  g.beginPath();
  g.moveTo(-r * 0.05, r * 0.22);
  g.lineTo(r * 0.05, r * 0.22);
  g.lineTo(0, r * 0.30);
  g.closePath();
  g.fill();

  /* دهان: فقط گربه‌ی خواننده متحرک است */
  const isSinger = cat.role === 'vocal';
  if (isSinger && cat.mouthOpen > 0.06) {
    const m = cat.mouthOpen;
    g.fillStyle = '#7a1220';
    g.beginPath();
    g.ellipse(0, r * 0.5, r * 0.16, r * 0.12 + m * r * 0.18, 0, 0, 7);
    g.fill();
    g.fillStyle = '#e06070';
    g.beginPath();
    g.ellipse(0, r * 0.56 + m * r * 0.10, r * 0.10, r * 0.05 + m * r * 0.06, 0, 0, 7);
    g.fill();
  } else {
    g.strokeStyle = '#1c1410';
    g.lineWidth = 0.018;
    g.beginPath();
    g.arc(-r * 0.10, r * 0.42, r * 0.13, 0.1, Math.PI - 0.1);
    g.stroke();
    g.beginPath();
    g.arc(r * 0.10, r * 0.42, r * 0.13, 0.1, Math.PI - 0.1);
    g.stroke();
  }

  /* سبیل */
  g.strokeStyle = 'rgba(255,255,255,.6)';
  g.lineWidth = 0.01;
  for (let s = -1; s <= 1; s += 2) {
    for (let j = -1; j <= 1; j++) {
      g.beginPath();
      g.moveTo(s * r * 0.55, r * 0.30 + j * 0.03);
      g.lineTo(s * r * 1.25, r * 0.26 + j * 0.06);
      g.stroke();
    }
  }

  /* اکسسوری سر بر اساس سبک */
  drawHeadAccessory(g, cat, style, r);
}

/* --- اکسسوری سر --- */
function drawHeadAccessory(g, cat, style, r) {
  const acc = style.clothes.accessory;

  // خواننده همیشه تاج دارد
  if (cat.role === 'vocal') {
    g.fillStyle = '#ffd24a';
    g.strokeStyle = '#b88a10';
    g.lineWidth = 0.012;
    g.beginPath();
    g.moveTo(-r * 0.55, -r * 0.9);
    g.lineTo(-r * 0.55, -r * 1.4);
    g.lineTo(-r * 0.28, -r * 1.15);
    g.lineTo(0, -r * 1.6);
    g.lineTo(r * 0.28, -r * 1.15);
    g.lineTo(r * 0.55, -r * 1.4);
    g.lineTo(r * 0.55, -r * 0.9);
    g.closePath();
    g.fill(); g.stroke();
    g.fillStyle = '#e0364f';
    g.beginPath();
    g.arc(0, -r * 1.15, r * 0.06, 0, 7);
    g.fill();
  }

  if (acc === 'bowtie') {
    const y = -r * 0.95;
    g.fillStyle = '#000';
    g.beginPath();
    g.moveTo(0, y); g.lineTo(-r * 0.18, y - r * 0.1); g.lineTo(-r * 0.18, y + r * 0.1);
    g.closePath(); g.fill();
    g.beginPath();
    g.moveTo(0, y); g.lineTo(r * 0.18, y - r * 0.1); g.lineTo(r * 0.18, y + r * 0.1);
    g.closePath(); g.fill();
  } else if (acc === 'headband') {
    g.fillStyle = '#fff';
    g.strokeStyle = '#000';
    g.lineWidth = 0.008;
    g.beginPath();
    g.rect(-r * 1.0, -r * 0.6, r * 2.0, r * 0.14);
    g.fill(); g.stroke();
  } else if (acc === 'fedora') {
    g.fillStyle = '#1a1414';
    g.beginPath();
    g.ellipse(0, -r * 0.85, r * 1.15, r * 0.2, 0, 0, 7);
    g.fill();
    g.fillStyle = '#2a2020';
    g.beginPath();
    g.roundRect(-r * 0.6, -r * 1.5, r * 1.2, r * 0.7, r * 0.1);
    g.fill();
    g.fillStyle = '#8a6a30';
    g.fillRect(-r * 0.6, -r * 1.05, r * 1.2, r * 0.12);
  } else if (acc === 'headset') {
    g.strokeStyle = '#20e0ff';
    g.lineWidth = 0.02;
    g.beginPath();
    g.arc(0, -r * 0.2, r * 1.05, Math.PI + 0.3, -0.3);
    g.stroke();
    g.fillStyle = '#20e0ff';
    g.beginPath(); g.arc(-r * 0.95, -r * 0.2, r * 0.18, 0, 7); g.fill();
    g.beginPath(); g.arc( r * 0.95, -r * 0.2, r * 0.18, 0, 7); g.fill();
  }
}


/* ============================================================================
   ۶) کلاس گربه
   ============================================================================ */

class Cat {
  constructor(def, index) {
    this.def = def;
    this.cfg = def.cfg;
    this.colors = def.colors;
    this.role = def.role;
    this.index = index;

    /* مکان و مقیاس */
    this.x = 0; this.y = 0; this.scale = 1;

    /* حرکات */
    this.phase = 0;
    this.mult = def.cfg.mult;
    this.offset = index * 1.4;
    this.energy = 0.15;
    this.jump = 0;
    this.jumpV = 0;
    this.lean = 0;
    this.leanTarget = 0;
    this.headNod = 0;
    this.headTilt = 0;
    this.squash = 1;
    this.frozen = 0;

    /* دست‌ها (زاویه‌ی شانه و آرنج) */
    this.armL = -0.6;
    this.armR = 0.6;
    this.elbowL = 0.5;
    this.elbowR = -0.5;

    /* دنباله */
    this.tailSegs = [0.2, 0.3, 0.4];

    /* صورت */
    this.mouthOpen = 0;
    this.eyeShut = 0;
    this.earL = 0;
    this.earR = 0;
    this.blinkT = rand(0, 4);

    /* نقشهٔ زمانی */
    this.strumCycle = 0;
    this.hitL = 0;
    this.hitR = 0;
    this.keyIdx = 0;

    /* سبک فعلی (برای دسترسی داخل draw) */
    this._style = null;
  }

  /* ------- به‌روزرسانی ------- */
  update(dt, t, A, style, playing) {
    const asleep = !playing || A.silence > 0.7;
    const bpmFactor = A.hasBpm ? A.bpm / 60 : 1.6;
    const sp = playing && !asleep ? 1 : 0.3;

    /* فاز گربه */
    this.phase += dt * Math.PI * 2 * bpmFactor * this.mult * sp * 0.5;

    /* قفل نرم روی ضرب (نه سخت) */
    if (playing && !asleep && A.pulse > 0.6) {
      const lockPhase = A.beat * Math.PI * this.mult + this.offset;
      this.phase = lerp(this.phase, lockPhase, clamp(dt * 4));
    }

    /* انرژی هدف */
    let targetEnergy = asleep
      ? 0.03
      : clamp(0.25 + A.sEnergy * 1.05) * (1 - A.silence * 0.5);
    if (this.frozen > 0) {
      targetEnergy *= 0.2;
      this.frozen -= dt;
    } else if (Math.random() < dt * 0.15 * (1 - A.sEnergy)) {
      this.frozen = rand(0.15, 0.5);
    }
    this.energy = smoothAR(this.energy, targetEnergy, 8, 3, dt);

    /* پرش: روی onsetهای قوی */
    if (playing && !asleep && A.pulse > 0.55 && A.bass > 0.35 && this.jump <= 0.01) {
      if (Math.random() < 0.25 + A.pulse * 0.6) {
        this.jumpV = -(0.25 + this.energy * 0.4 + A.pulse * 0.3) * (0.5 + this.mult * 0.4);
      }
    }

    /* فیزیک پرش (بدون پرش برای درامر) */
    if (this.role !== 'drums') {
      this.jumpV += 4.2 * dt;
      this.jump += this.jumpV * dt;
      if (this.jump >= 0) { this.jump = 0; this.jumpV = 0; }
    } else {
      this.jump = Math.max(0, this.jump - dt * 3);
    }

    /* اسکواش / کشش */
    const targetSq = this.jump < -0.02 ? 1.10 : (A.pulse > 0.6 ? 0.92 : 1);
    this.squash = smooth(this.squash, targetSq, 12, dt);

    /* تکیه */
    let leanTarget = asleep
      ? 0.25
      : (this.role === 'drums' ? 0.08
        : this.role === 'keys' ? 0.15
        : 0) + Math.sin(this.phase * 0.5) * 0.06 * this.energy;
    this.lean = smooth(this.lean, leanTarget, 4, dt);

    /* نوسان سر */
    const nodTarget = asleep ? 0.25 : Math.sin(this.phase * 1.2) * 0.12 * this.energy;
    this.headNod = smooth(this.headNod, nodTarget, 8, dt);

    const tiltTarget = asleep
      ? 0.35
      : Math.sin(this.phase * 0.35 + 1) * 0.12 * this.energy;
    this.headTilt = smooth(this.headTilt, tiltTarget, 4, dt);

    /* دنباله */
    for (let i = 0; i < 3; i++) {
      const s = Math.sin(this.phase * 0.6 + i * 0.7 + t * 0.5) * (0.25 + this.energy * 0.6);
      this.tailSegs[i] = smooth(this.tailSegs[i], s, 3 - i * 0.6, dt);
    }

    /* رفتار اختصاصی */
    this.updateRole(dt, t, A, style, asleep);

    /* چهره */
    if (this.role === 'vocal') {
      // لب فقط وقتی A.vocal > 0.1 باز می‌شود
      const env = A.vocal > 0.1
        ? clamp(A.vocal * 1.6 + A.rms * 1.5) * (0.8 + 0.2 * Math.sin(t * 20 + this.index))
        : 0;
      this.mouthOpen = smoothAR(this.mouthOpen, env, 22, 14, dt);
    } else {
      this.mouthOpen = smooth(this.mouthOpen, 0, 6, dt);
    }
    this.eyeShut = smooth(this.eyeShut, asleep ? 1 : 0, 3, dt);
    this.blinkT += dt;
    if (this.blinkT > rand(2.5, 4.5)) this.blinkT = 0;
    this.earL = smooth(this.earL, Math.sin(t * 2.2 + this.index) * 0.1, 2, dt);
    this.earR = smooth(this.earR, Math.sin(t * 2.0 + this.index + 1) * 0.1, 2, dt);
  }

  /* ------- رفتار اختصاصی هر نقش ------- */
  updateRole(dt, t, A, style, asleep) {
    const e = this.energy;
    const p = this.phase;
    const bpm = A.hasBpm ? A.bpm / 60 : 1.5;

    if (asleep) {
      this.armL = smooth(this.armL, -0.4, 3, dt);
      this.elbowL = smooth(this.elbowL, 0.4, 3, dt);
      this.armR = smooth(this.armR, 0.4, 3, dt);
      this.elbowR = smooth(this.elbowR, -0.4, 3, dt);
      return;
    }

    switch (this.role) {
      case 'guitar': {
        // دست چپ روی فرت (بالا)، دست راست می‌زند (پایین)
        const strumRate = 1 + A.sEnergy * 2;
        this.strumCycle += dt * strumRate * bpm;
        const strumPhase = Math.sin(this.strumCycle * Math.PI * 2);

        const targetL = -1.4 + Math.sin(p * 0.5) * 0.15 * e;
        const targetR = 0.3 + strumPhase * 0.35 * (0.5 + e);
        this.armL   = smoothAR(this.armL,   targetL, 8, 4, dt);
        this.elbowL = smoothAR(this.elbowL, 0.9 + Math.sin(p * 0.7) * 0.1, 8, 4, dt);
        this.armR   = smoothAR(this.armR,   targetR, 14, 6, dt);
        this.elbowR = smoothAR(this.elbowR, -0.6 + strumPhase * 0.2, 14, 6, dt);
        break;
      }
      case 'drums': {
        // دو دست متناوب روی کیت
        const hitRate = 1 + A.sEnergy * 3;
        this.hitL += dt * hitRate * 2;
        this.hitR += dt * hitRate * 2 + 0.5;
        const sl = Math.sin(this.hitL * Math.PI * 2);
        const sr = Math.sin(this.hitR * Math.PI * 2);

        this.armL   = smoothAR(this.armL,   -0.9 + sl * 0.5, 20, 8, dt);
        this.elbowL = smoothAR(this.elbowL,  0.9 + Math.abs(sl) * 0.3, 20, 8, dt);
        this.armR   = smoothAR(this.armR,    0.9 - sr * 0.5, 20, 8, dt);
        this.elbowR = smoothAR(this.elbowR, -0.9 - Math.abs(sr) * 0.3, 20, 8, dt);
        break;
      }
      case 'vocal': {
        // دست چپ میکروفون، دست راست آزاد
        this.armL   = smoothAR(this.armL,   -1.6 - Math.sin(p * 0.5) * 0.25 * e, 6, 4, dt);
        this.elbowL = smoothAR(this.elbowL,  1.15, 6, 4, dt);
        this.armR   = smoothAR(this.armR,    0.6 + Math.sin(p * 0.4 + 0.5) * 0.4 * e, 5, 3, dt);
        this.elbowR = smoothAR(this.elbowR, -0.7, 5, 3, dt);
        break;
      }
      case 'keys': {
        // دو دست روی کیبورد
        const kRate = 1.2 + A.sEnergy * 2;
        this.keyIdx += dt * kRate;
        this.armL   = smoothAR(this.armL,   -1.1 + Math.sin(this.keyIdx * 4) * 0.12 * e, 16, 6, dt);
        this.elbowL = smoothAR(this.elbowL,  0.95 + Math.sin(this.keyIdx * 4 + 1) * 0.1, 16, 6, dt);
        this.armR   = smoothAR(this.armR,    1.1 - Math.sin(this.keyIdx * 4 + 1.7) * 0.12 * e, 16, 6, dt);
        this.elbowR = smoothAR(this.elbowR, -0.95 - Math.sin(this.keyIdx * 4 + 2) * 0.1, 16, 6, dt);
        break;
      }
      case 'bass': {
        // مثل گیتار ولی آرام‌تر
        const strumRate = 1 + A.sEnergy * 1.2;
        this.strumCycle += dt * strumRate * bpm;
        const ph = Math.sin(this.strumCycle * Math.PI * 2);
        this.armL   = smoothAR(this.armL,   -1.3 + Math.sin(p * 0.4) * 0.1, 6, 4, dt);
        this.elbowL = smoothAR(this.elbowL,  0.85, 6, 4, dt);
        this.armR   = smoothAR(this.armR,    0.5 + ph * 0.25 * (0.5 + e), 10, 5, dt);
        this.elbowR = smoothAR(this.elbowR, -0.7 + ph * 0.15, 10, 5, dt);
        break;
      }
    }
  }

  /* ------- رسم ------- */
  draw(g, style, t) {
    const c = this.cfg;
    const col = this.colors;
    const S = this.scale;
    const legLen = c.legLen;
    const bodyH = c.bodyH;
    const bodyW = c.bodyW;
    const headR = c.headR;

    g.save();
    g.translate(this.x, this.y);
    g.scale(S, S);

    /* اسکواش حول زمین */
    const sq = this.squash;
    g.scale(1 / sq, sq);

    /* سایه */
    const shadowScale = 1 + this.jump * 0.6;
    g.fillStyle = 'rgba(0,0,0,0.4)';
    g.beginPath();
    g.ellipse(0, 0, bodyW * 0.62 * shadowScale, 0.055 * shadowScale, 0, 0, 7);
    g.fill();

    /* هیپ = نقطهٔ مرجع همه چیز */
    const jumpY = -this.jump;
    const hipX = 0;
    const hipY = -legLen - jumpY;

    /* پاها */
    drawLeg(g, this, hipX - bodyW * 0.28, hipY, -1);
    drawLeg(g, this, hipX + bodyW * 0.28, hipY,  1);

    /* دنباله */
    drawTail(g, this, hipX + bodyW * 0.30, hipY - bodyH * 0.05);

    /* بدن (چرخش حول هیپ) */
    g.save();
    g.translate(hipX, hipY);
    g.rotate(this.lean + this.headNod * 0.1);
    g.translate(0, -bodyH * 0.42);

    /* شکم */
    g.fillStyle = col.body;
    g.beginPath();
    g.ellipse(0, 0, bodyW * 0.5, bodyH * 0.48, 0, 0, 7);
    g.fill();
    g.fillStyle = col.belly;
    g.beginPath();
    g.ellipse(0, bodyH * 0.1, bodyW * 0.28, bodyH * 0.36, 0, 0, 7);
    g.fill();

    /* الگو */
    drawPattern(g, this, bodyW, bodyH);

    /* لباس */
    drawClothes(g, this, style, bodyW, bodyH);

    /* بازوها */
    const shLX = -bodyW * 0.42;
    const shRX = bodyW * 0.42;
    const shY  = -bodyH * 0.25;
    const armL = solveArm(shLX, shY, this.armL, this.elbowL, 0.34, 0.30);
    const armR = solveArm(shRX, shY, this.armR, this.elbowR, 0.34, 0.30);

    /* دست پشتی */
    drawArm(g, this, armL);

    /* ساز */
    const gtr = style.guitar;
    if (this.role === 'guitar' && gtr) {
      drawGuitar(g, gtr, armL, armR);
    } else if (this.role === 'bass' && gtr) {
      drawGuitar(g, 'bass', armL, armR);
    } else if (this.role === 'drums') {
      drawDrumKit(g, this, bodyW, bodyH);
    } else if (this.role === 'vocal') {
      drawMic(g, armL);
    } else if (this.role === 'keys') {
      if (style.hasPiano) drawKeyboard(g, this, bodyW, styleKey(style));
      else drawAmp(g, bodyW);
    }
    /* در راک و هیپ‌هاپ: گیتاریست/بیسیست بدون ساز → ژست رپر */
    if (this.role === 'guitar' && !gtr) drawMic(g, armL);

    /* آمپ برای گیتاریست راک */
    if (style.hasAmp && this.role === 'guitar') {
      drawAmp(g, bodyW);
    }

    /* دست جلویی */
    drawArm(g, this, armR);

    /* سر */
    g.save();
    g.translate(0, -bodyH * 0.6);
    g.rotate(this.headTilt);
    g.translate(0, -headR * 0.7);
    drawHead(g, this, style, t);
    g.restore();

    g.restore(); /* پایان چرخش بدن */
    g.restore(); /* پایان ترنسفورم گربه */
  }
}

/* تشخیص نوع کیبورد از سبک */
function styleKey(style) {
  return style === STYLES.electronic ? 'electronic' : 'classic';
}


/* ============================================================================
   ۷) صحنه و حلقهٔ رندر
   ============================================================================ */

const cv = $('#cv'), g = cv.getContext('2d');
const vu = $('#vu'), vg = vu.getContext('2d');
const stageEl = $('#stage');
const au = $('#au');

let W = 0, H = 0, D = 1;
function fitCanvas() {
  D = Math.min(window.devicePixelRatio || 1, 2);
  for (const c of [cv, vu]) {
    c.width = c.clientWidth * D;
    c.height = c.clientHeight * D;
  }
  W = cv.width / D;
  H = cv.height / D;
}
window.addEventListener('resize', fitCanvas);
fitCanvas();

const CATS = CAT_DEFS.map((d, i) => new Cat(d, i));
const A = new AudioEngine(au);
const parts = new Particles();

const state = {
  style: 'rock',
  playing: false
};

let lastT = performance.now();
let reel = 0;
let shakeAmount = 0;
let shakeX = 0, shakeY = 0;
let lastVib = 0;
let hueCur = null;

/* رنگ آسمان بر اساس سبک و انرژی */
function chooseHue() {
  const map = { rock: 8, pop: 330, classic: 40, jazz: 25, electronic: 195, hiphop: 45 };
  const base = map[state.style] || 30;
  return (base + A.sEnergy * 30 + 360) % 360;
}

/* حالت و هوا */
function mood() {
  if (!state.playing || A.silence > 0.7) return ['خواب‌آلود', 230];
  if (state.style === 'rock' && A.sEnergy > 0.4) return ['خشن و طوفانی', 8];
  if (A.sEnergy > 0.5) return ['شاد و پرشور', chooseHue()];
  if (A.sEnergy > 0.25) return ['سرخوش', chooseHue()];
  return ['آرام و رؤیایی', 220];
}

function render(dt, t) {
  const style = STYLES[state.style];
  const fx = style.effects;

  /* شیک */
  const shk = state.playing && A.silence < 0.5
    ? (A.pulse * A.sEnergy * 12 * fx.shake + A.sEnergy * 2) * (1 - A.silence)
    : 0;
  shakeAmount = smooth(shakeAmount, shk, 12, dt);
  shakeX = (Math.random() - 0.5) * shakeAmount;
  shakeY = (Math.random() - 0.5) * shakeAmount;

  /* پس‌زمینه */
  g.setTransform(D, 0, 0, D, 0, 0);
  g.clearRect(0, 0, W, H);
  g.save();
  g.translate(shakeX, shakeY);

  const targetHue = chooseHue();
  if (hueCur === null) hueCur = targetHue;
  else hueCur += wrap((targetHue - hueCur) * Math.PI / 180) * 180 / Math.PI * clamp(dt * 1.5);
  const hu = hueCur;
  const eN = A.sEnergy;

  const bgGrad = g.createLinearGradient(0, 0, 0, H);
  bgGrad.addColorStop(0, `hsl(${hu} 40% ${5 + eN * 10}%)`);
  bgGrad.addColorStop(1, `hsl(${hu + 20} 35% ${11 + eN * 12}%)`);
  g.fillStyle = bgGrad;
  g.fillRect(-40, -40, W + 80, H + 80);

  /* زمین */
  g.fillStyle = `hsl(${hu} 25% 8%)`;
  g.fillRect(-40, H * 0.78, W + 80, H);

  /* خطوط زمین */
  g.strokeStyle = 'rgba(255,255,255,.06)';
  g.lineWidth = 1;
  for (let i = 0; i < 8; i++) {
    g.beginPath();
    g.moveTo(0, H * 0.8 + i * i * 2.2);
    g.lineTo(W, H * 0.8 + i * i * 2.2);
    g.stroke();
  }

  /* نورافکن‌ها */
  g.globalCompositeOperation = 'lighter';
  const on = state.playing && A.silence < 0.4;
  for (let i = 0; i < 6; i++) {
    const x0 = W * (i + 0.5) / 6;
    const ang = Math.sin(t * (0.6 + i * 0.08) + i * 1.3) * (0.28 + 0.3 * eN);
    const wd = W * (0.05 + 0.05 * eN);
    const xe = x0 + Math.tan(ang) * H * 1.05;
    const beamHue = (hu + i * 38) % 360;
    const alpha = on ? (0.08 + 0.28 * eN + A.pulse * 0.28 * fx.shake) : 0.05;

    const gr = g.createLinearGradient(x0, 0, xe, H);
    gr.addColorStop(0, `hsla(${beamHue},95%,65%,${alpha})`);
    gr.addColorStop(1, `hsla(${beamHue},95%,60%,0)`);
    g.fillStyle = gr;
    g.beginPath();
    g.moveTo(x0 - 5, 0);
    g.lineTo(x0 + 5, 0);
    g.lineTo(xe + wd, H);
    g.lineTo(xe - wd, H);
    g.fill();

    g.fillStyle = `hsla(${beamHue},95%,60%,${on ? 0.1 + 0.2 * eN : 0.04})`;
    g.beginPath();
    g.ellipse(xe, H * 0.9, wd * 1.4, H * 0.04, 0, 0, 7);
    g.fill();
  }
  g.globalCompositeOperation = 'source-over';

  /* فلاش راک */
  if (state.style === 'rock' && A.pulse > 0.8 && on) {
    g.fillStyle = `rgba(255,255,255,${0.1 * A.sEnergy * fx.shake})`;
    g.fillRect(0, 0, W, H);
  }

  /* گربه‌ها */
  const Sz = Math.min(W / 5.3, H * 0.62);
  for (let i = 0; i < CATS.length; i++) {
    const cat = CATS[i];
    cat._style = style;
    cat.x = W * (0.1 + 0.2 * i) + Math.sin(t * 0.35 + i * 2) * W * 0.02 * (1 - A.silence);
    cat.y = H * 0.94;
    cat.scale = Sz;
    cat.draw(g, style, t);

    /* نشانگر خواب */
    if (A.silence > 0.6) {
      g.fillStyle = 'rgba(255,255,255,.8)';
      g.font = `${Sz * 0.2}px Lalezar`;
      g.fillText('z', cat.x + Sz * 0.2, cat.y - Sz * cat.cfg.bodyH * (1.0 + 0.1 * Math.sin(t * 2 + i)));
    }
  }

  /* ذرات */
  parts.draw(g);

  g.restore();

  /* شیک صحنه */
  if (shakeAmount > 0.3) {
    stageEl.style.transform = `translate(${shakeX * 0.4}px, ${shakeY * 0.4}px)`;
  } else if (stageEl.style.transform) {
    stageEl.style.transform = '';
  }

  /* ارتعاش موبایل */
  if (state.style === 'rock' && A.sEnergy > 0.5 && A.pulse > 0.9 &&
      t - lastVib > 0.25 && navigator.vibrate) {
    try { navigator.vibrate(15 + A.sEnergy * 30); } catch (e) {}
    lastVib = t;
  }
}

/* VU */
function drawVU(t) {
  vg.setTransform(D, 0, 0, D, 0, 0);
  const vw = vu.width / D, vh = vu.height / D;
  vg.clearRect(0, 0, vw, vh);
  const N = 40;
  for (let i = 0; i < N; i++) {
    const v = A.connected && state.playing
      ? A.freq[Math.floor(Math.pow(i / N, 1.7) * 220) + 1] / 255
      : 0.03;
    const h = Math.max(3, v * vh * (0.85 + 0.15 * Math.sin(t * 5 + i)));
    const hue = (hueCur || 40) + i * 3;
    vg.fillStyle = `hsl(${hue} 80% ${50 + v * 15}%)`;
    const bw = vw / N;
    const x = i * bw + 2;
    const y = vh - h;
    const w = bw - 4;
    vg.beginPath();
    vg.roundRect(x, y, w, h, 3);
    vg.fill();
  }
}

/* ذرات */
function spawnParticles() {
  if (!state.playing || A.silence > 0.5) return;
  if (A.pulse < 0.5) return;
  const style = STYLES[state.style];
  const ptype = style.effects.particles;
  const n = 1 + Math.floor(A.sEnergy * 3);
  for (let k = 0; k < n; k++) {
    const i = Math.floor(Math.random() * CATS.length);
    const cat = CATS[i];
    if (Math.random() < 0.3 + A.sEnergy * 0.5) {
      parts.spawn(
        ptype,
        cat.x + rand(-0.2, 0.2) * cat.scale,
        cat.y - cat.scale * 0.9,
        hueCur || 40
      );
    }
  }
}

/* HUD */
let hudT = 0;
function hud(t) {
  if (t - hudT < 0.2) return;
  hudT = t;
  const [m] = mood();
  let gen = 'منتظر موزیک…';
  if (state.playing) {
    if (A.silence > 0.6) gen = 'سکوت…';
    else if (state.style === 'rock' && A.sEnergy > 0.55) gen = '🤘 راک سنگین — لرزش کامل';
    else if (state.style === 'rock' && A.sEnergy > 0.3) gen = 'گیتار برقی و انرژی';
    else if (A.sEnergy > 0.45) gen = 'پرانرژی و شاد';
    else if (A.sEnergy > 0.2) gen = 'ملایم و روان';
    else gen = 'آرام';
  }
  $('#badge').textContent = gen;
  $('#mm').textContent = m;
  $('#mb').textContent = state.playing && A.hasBpm ? fa(A.bpm) : '—';
  $('#me').textContent = fa(A.sEnergy * 100);
  $('#ue').style.width = (A.sEnergy * 100) + '%';
}

/* حلقه */
function tick(now) {
  requestAnimationFrame(tick);
  const dt = Math.min(0.05, (now - lastT) / 1000);
  lastT = now;
  const t = now / 1000;

  A.update(dt, t, state.playing);

  const style = STYLES[state.style];
  for (const c of CATS) c.update(dt, t, A, style, state.playing);

  spawnParticles();
  parts.update(dt);

  /* رکوردها */
  if (state.playing && A.silence < 0.5) {
    reel += dt * (40 + A.bpm * 0.7 * (0.5 + A.sEnergy));
  } else {
    reel += dt * 8;
  }
  $('#r1').style.transform = `rotate(${reel}deg)`;
  $('#r2').style.transform = `rotate(${reel * 0.8}deg)`;

  render(dt, t);
  drawVU(t);
  hud(t);
}
requestAnimationFrame(tick);


/* ============================================================================
   ۸) پلیر
   ============================================================================ */

const list = [];
let cur = -1;

const mmss = s => isFinite(s)
  ? fa(Math.floor(s / 60)) + ':' + fa(Math.floor(s % 60)).padStart(2, '۰')
  : '۰:۰۰';

function addFiles(files) {
  let added = false;
  for (const f of files) {
    if (!f.type.startsWith('audio') &&
        !/\.(mp3|wav|ogg|m4a|flac|aac|opus)$/i.test(f.name)) continue;
    list.push({
      name: f.name.replace(/\.[^.]+$/, ''),
      url: URL.createObjectURL(f)
    });
    added = true;
  }
  if (added) {
    drawList();
    if (cur < 0 && list.length) {
      load(0, false);
      openStyleModal();
    }
  }
}

function drawList() {
  const ul = $('#list');
  ul.innerHTML = '';
  list.forEach((s, i) => {
    const li = document.createElement('li');
    li.className = i === cur ? 'cur' : '';
    li.innerHTML = '<span></span><span>' + fa(i + 1) + '</span>';
    li.firstChild.textContent = s.name;
    li.onclick = () => load(i, true);
    ul.appendChild(li);
  });
}

function load(i, go) {
  if (!list.length) return;
  cur = (i + list.length) % list.length;
  const item = list[cur];
  au.src = item.url;
  $('#title').textContent = item.name;
  $('#sub').textContent = 'در حال تحلیل ریتم و حال‌وهوا…';
  A.reset();
  drawList();
  if (go) play();
}

async function play() {
  A.connect();
  await A.resume();
  if (au.src) {
    try { await au.play(); } catch (e) {}
  }
}

function setIcon(isPlaying) {
  $('#ic').innerHTML = isPlaying
    ? '<path d="M6 4h4v16H6zM14 4h4v16h-4z"/>'
    : '<path d="M7 4v16l13-8z"/>';
}

au.onplay  = () => { state.playing = true;  setIcon(true);  };
au.onpause = () => { state.playing = false; setIcon(false); };
au.onended = () => {
  if (list.length > 1) load(cur + 1, true);
  else { state.playing = false; setIcon(false); }
};

/* تایم‌لاین کاغذی */
let seeking = false;
const trackEl = $('#track');
const fillEl  = $('#fill');
const pinEl   = $('#pin');

function updateTimeline() {
  if (!seeking) {
    const p = au.duration ? au.currentTime / au.duration : 0;
    fillEl.style.width = (p * 100) + '%';
    pinEl.style.right  = (p * 100) + '%';
  }
  $('#tc').textContent = mmss(au.currentTime);
  $('#td').textContent = mmss(au.duration);
}
au.ontimeupdate = updateTimeline;

function seekAt(clientX) {
  const r = trackEl.getBoundingClientRect();
  // RTL: از راست شروع می‌شود
  let p = 1 - (clientX - r.left) / r.width;
  p = clamp(p);
  if (au.duration) au.currentTime = p * au.duration;
  fillEl.style.width = (p * 100) + '%';
  pinEl.style.right  = (p * 100) + '%';
}

trackEl.addEventListener('pointerdown', e => {
  seeking = true;
  trackEl.classList.add('dragging');
  seekAt(e.clientX);
  try { trackEl.setPointerCapture(e.pointerId); } catch (_) {}
});
trackEl.addEventListener('pointermove', e => {
  if (seeking) seekAt(e.clientX);
});
function endSeek(e) {
  if (!seeking) return;
  seeking = false;
  trackEl.classList.remove('dragging');
  try { trackEl.releasePointerCapture(e.pointerId); } catch (_) {}
}
trackEl.addEventListener('pointerup', endSeek);
trackEl.addEventListener('pointercancel', endSeek);

/* کیبورد روی تایم‌لاین */
trackEl.addEventListener('keydown', e => {
  if (!au.duration) return;
  if (e.key === 'ArrowLeft')  { au.currentTime = clamp(au.currentTime / au.duration - 0.02) * au.duration; }
  if (e.key === 'ArrowRight') { au.currentTime = clamp(au.currentTime / au.duration + 0.02) * au.duration; }
  if (e.key === 'Home')       { au.currentTime = 0; }
  if (e.key === 'End')        { au.currentTime = au.duration; }
});

/* دکمه‌ها */
$('#play').onclick = () => au.paused ? play() : au.pause();
$('#prev').onclick = () => load(cur - 1, true);
$('#next').onclick = () => load(cur + 1, true);

$('#vol').oninput = e => { au.volume = e.target.value / 100; };
au.volume = 0.85;
$('#vol').value = 85;

/* فایل */
$('#file').onchange = e => addFiles(e.target.files);
for (const el of [$('#drop'), stageEl]) {
  el.addEventListener('dragover', e => {
    e.preventDefault();
    $('#drop').classList.add('on');
  });
  el.addEventListener('dragleave', () => $('#drop').classList.remove('on'));
  el.addEventListener('drop', e => {
    e.preventDefault();
    $('#drop').classList.remove('on');
    if (e.dataTransfer && e.dataTransfer.files) addFiles(e.dataTransfer.files);
  });
}


/* ============================================================================
   ۹) مودال انتخاب سبک
   ============================================================================ */

function buildStyleGrid() {
  const grid = $('#styleGrid');
  grid.innerHTML = '';
  for (const [key, s] of Object.entries(STYLES)) {
    const card = document.createElement('div');
    card.className = 'style-card';
    card.setAttribute('role', 'button');
    card.setAttribute('tabindex', '0');
    card.innerHTML = `
      <div class="swatch" style="background:${s.swatch}"></div>
      ${s.icon}
      <b>${s.name}</b>
      <span>${s.tagline}</span>
    `;
    const select = () => {
      state.style = key;
      const cur = $('#styleName');
      cur.textContent = 'سبک: ' + s.name;
      // رنگ نقطهٔ رنگی کنار متن
      cur.style.setProperty('--hot', s.accent);
      cur.querySelector('::before');
      hueCur = null;
      closeStyleModal();
    };
    card.onclick = select;
    card.onkeydown = e => {
      if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); select(); }
    };
    grid.appendChild(card);
  }
}

function openStyleModal() {
  const m = $('#modal');
  m.classList.add('on');
  m.setAttribute('aria-hidden', 'false');
}
function closeStyleModal() {
  const m = $('#modal');
  m.classList.remove('on');
  m.setAttribute('aria-hidden', 'true');
  // اگر آهنگ لود شده ولی پخش نشده، شروع کن
  if (au.src && au.paused && list.length) play();
}

$('#modal').addEventListener('click', e => {
  if (e.target.id === 'modal') closeStyleModal();
});
document.addEventListener('keydown', e => {
  if (e.key === 'Escape' && $('#modal').classList.contains('on')) closeStyleModal();
});
$('#styleBtn').onclick = openStyleModal;


/* ============================================================================
   ۱۰) راه‌اندازی
   ============================================================================ */

buildStyleGrid();
drawList();

/* مقداردهی اولیه سنجه‌ها */
$('#mb').textContent = '—';
$('#me').textContent = '۰';
$('#mm').textContent = '—';
