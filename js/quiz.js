/* Motor dos quizzes: não precisa mexer aqui. */
function montaQuiz(el, perguntas){
  let i = 0, acertos = 0;
  function render(){
    if (i >= perguntas.length){
      el.innerHTML = `<p class="q">Você acertou <b>${acertos}</b> de ${perguntas.length}.</p>
        <button class="btn next" id="rec">Recomeçar</button>`;
      el.querySelector('#rec').onclick = () => { i = 0; acertos = 0; render(); };
      return;
    }
    const p = perguntas[i];
    el.innerHTML = `<div class="top"><span>Pergunta ${i+1} de ${perguntas.length}</span><span>Acertos: ${acertos}</span></div>
      <div class="q">${p.q}</div>
      ${p.opcoes.map((o,k)=>`<button class="opt" data-k="${k}">${o}</button>`).join('')}
      <div class="fb"></div>`;
    el.querySelectorAll('.opt').forEach(b => b.onclick = () => {
      const k = +b.dataset.k, ok = k === p.certa;
      if (ok) acertos++;
      el.querySelectorAll('.opt').forEach(x => { x.disabled = true;
        if (+x.dataset.k === p.certa) x.classList.add('ok'); });
      if (!ok) b.classList.add('bad');
      const fb = el.querySelector('.fb');
      fb.innerHTML = `<b class="${ok?'ok':'bad'}">${ok?'Correto.':'Não é essa.'}</b> ${p.exp}
        <div><button class="btn next">${i+1<perguntas.length?'Próxima':'Ver resultado'}</button></div>`;
      fb.querySelector('.next').onclick = () => { i++; render(); };
      if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([fb]);
    });
    if (window.MathJax && MathJax.typesetPromise) MathJax.typesetPromise([el]);
  }
  render();
}
