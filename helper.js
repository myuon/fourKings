function jsSetInnerText(elem, context) {
  if (elem.innerText == undefined) { elem.textContent = context; }
  else { elem.innerText = context; }
}
