// Run after setting prefers-reduced-motion to reduce through browser emulation.
// Restore emulation after collecting the result.
JSON.stringify({
  reducedMotion: matchMedia('(prefers-reduced-motion: reduce)').matches,
  animations: [...document.querySelectorAll('.tube-anim')].map(x => getComputedStyle(x).display),
  finals: [...document.querySelectorAll('.tube-end')].map(x => getComputedStyle(x).display),
  boards: ['f-score-fork', 'f-score-two', 'f-queue2', 'f-queue13'].map(id => {
    const svg = document.getElementById(id);
    return {
      id,
      paths: svg.querySelectorAll('path').length,
      pathAnimations: svg.querySelectorAll('animate[attributeName="d"]').length,
      nonDiscrete: [...svg.querySelectorAll('animate')].filter(a => a.getAttribute('calcMode') !== 'discrete').length,
      missingReferences: [...svg.querySelectorAll('use')].filter(u =>
        !document.getElementById((u.getAttribute('href') || '').slice(1))).length
    };
  })
});
