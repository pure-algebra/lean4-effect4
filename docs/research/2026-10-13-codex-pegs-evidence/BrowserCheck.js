// Run in the browser after opening the generated tubes.html.
// The check mutates SVG clocks. Reload the page after collecting its result.
// This is finite browser evidence, not a theorem about SMIL.
(() => {
  const results = [];
  const normalize = value => value === 'none' ? 'none' :
    value.split(/[ ,]+/).map(Number.parseFloat).join(',');
  for (const id of ['f-score-fork', 'f-score-two', 'f-queue2', 'f-queue13']) {
    const svg = document.getElementById(id);
    svg.pauseAnimations();
    let checked = 0;
    const errors = [];
    for (const animation of svg.querySelectorAll('animate')) {
      const times = animation.getAttribute('keyTimes').split(';').map(Number);
      const values = animation.getAttribute('values').split(';');
      const begin = parseFloat(animation.getAttribute('begin')) / 1000;
      const duration = parseFloat(animation.getAttribute('dur')) / 1000;
      const attribute = animation.getAttribute('attributeName');
      for (let i = 0; i < values.length; i++) {
        const time = begin + duration * times[i] + 0.001;
        svg.setCurrentTime(time);
        const actual = getComputedStyle(animation.parentElement).getPropertyValue(attribute).trim();
        checked++;
        if (normalize(actual) !== normalize(values[i])) {
          errors.push({ attribute, time, expected: values[i], actual });
        }
      }
    }
    results.push({ id, checked, errors });
  }
  return JSON.stringify(results);
})();
