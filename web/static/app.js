// Ledger Kernel web UI: browse a world's entries, view proofs as a table or
// as a proof tree, and check proofs typed in the editor. All logic that
// decides anything lives on the server (the kernel); this file only displays.
"use strict";

const state = {
  world: "zf",
  entries: [],
  selectedK: null,
  editorMode: "table",
  lastCheck: null,
};

const KIND_GROUPS = {
  theorem: ["th", "th-ded"],
  axiom: ["axiom"],
  rule: ["irule"],
  formation: ["wff?", "term?", "var?"],
  symbol: ["atomic-wff-symbol", "variable-symbol", "predicate-schema-symbol"],
};
const KIND_LABELS = {
  "th": "定理", "th-ded": "定理（演繹）",
  "axiom": "公理", "irule": "推論規則", "wff?": "論理式の形成", "term?": "項の形成",
  "var?": "変数の形成", "atomic-wff-symbol": "命題記号", "variable-symbol": "変数",
  "predicate-schema-symbol": "述語スキーマ",
};
const ROLE_LABELS = { hyp: "仮定", axiom: "公理", ir: "規則", th: "定理", "th-ded": "定理" };

// --- small helpers ------------------------------------------------------------

function el(tag, attrs = {}, ...children) {
  const e = document.createElement(tag);
  for (const [k, v] of Object.entries(attrs)) {
    if (k === "class") e.className = v;
    else if (k.startsWith("on")) e.addEventListener(k.slice(2), v);
    else if (v !== undefined && v !== null) e.setAttribute(k, v);
  }
  for (const c of children.flat()) {
    if (c === null || c === undefined || c === false) continue;
    e.append(c instanceof Node ? c : document.createTextNode(String(c)));
  }
  return e;
}

// A static export (web/static-export.lisp) sets window.LEDGER_STATIC and
// ships every answer the server would give as data/*.js; the page is then
// read-only, since checking a new proof needs the kernel.
const STATIC = window.LEDGER_STATIC || null;

function loadStaticWorld(id) {
  if (STATIC.data[id]) return Promise.resolve(STATIC.data[id]);
  if (!/^[\w-]+$/.test(id)) return Promise.reject(new Error("unknown world " + id));
  return new Promise((resolve, reject) => {
    const s = document.createElement("script");
    s.src = `data/${id}.js`;
    s.onload = () => STATIC.data[id] ? resolve(STATIC.data[id]) : reject(new Error("no data for " + id));
    s.onerror = () => reject(new Error(`data/${id}.js を読み込めません`));
    document.head.append(s);
  });
}

async function staticApi(path) {
  const u = new URL(path, "http://static.invalid/");
  if (u.pathname === "/api/worlds") return STATIC.worlds;
  if (u.pathname === "/api/check") throw new Error("静的版では証明を検証できません（サーバー版 tools/serve.lisp で検証できます）。");
  const data = await loadStaticWorld(u.searchParams.get("world"));
  if (u.pathname === "/api/entries") return data.entries;
  if (u.pathname === "/api/entry") {
    const e = data.entry[u.searchParams.get("k")];
    if (!e) throw new Error("No entry " + u.searchParams.get("k"));
    return e;
  }
  throw new Error("unknown path " + path);
}

async function api(path, options) {
  if (STATIC) return staticApi(path);
  const res = await fetch(path, options);
  const data = await res.json();
  if (!res.ok) throw new Error(data.error || res.statusText);
  return data;
}

// Links to entries open in a new tab, so a chain of definitions and
// lemmas can be followed recursively while the current page stays put.
function entryHref(k) { return `#${state.world}/${k}`; }

function entryLink(k, text, attrs = {}) {
  return el("a", { href: entryHref(k), target: "_blank", rel: "noopener", ...attrs }, text);
}

// A formula as text whose symbols and operators link to the entry that
// introduced them (declaration, formation rule, or definition).
function formulaNode(f) {
  if (!f.segments) return document.createTextNode(f.text);
  const span = el("span", { class: "formula" });
  for (const seg of f.segments) {
    span.append(seg.k ? entryLink(seg.k, seg.t, { class: "sym", title: `#${seg.k} を新しいタブで開く` })
                      : document.createTextNode(seg.t));
  }
  return span;
}

function joinNodes(nodes, sep) {
  return nodes.flatMap((n, i) => (i ? [sep, n] : [n]));
}

function kindGroup(kind) {
  for (const [g, kinds] of Object.entries(KIND_GROUPS)) if (kinds.includes(kind)) return g;
  return "symbol";
}

// --- worlds and the entry list ----------------------------------------------------

async function loadWorlds() {
  const worlds = await api("/api/worlds");
  state.worlds = worlds;
  const select = document.getElementById("world");
  select.replaceChildren(...worlds.map(w => el("option", { value: w.id }, `${w.title}（${w.entries}）`)));
  const fromHash = parseHash();
  if (fromHash && worlds.some(w => w.id === fromHash.world)) state.world = fromHash.world;
  select.value = state.world;
  select.addEventListener("change", () => { state.world = select.value; state.selectedK = null; loadEntries(); });
  await loadEntries();
  if (fromHash && fromHash.k) showEntry(fromHash.k);
}

async function loadEntries() {
  state.entries = await api(`/api/entries?world=${encodeURIComponent(state.world)}`);
  renderList();
  if (!state.selectedK) {
    document.getElementById("entry-detail").replaceChildren(
      intro());
  }
}

function activeFilters() {
  const on = {};
  document.querySelectorAll(".filters input").forEach(i => on[i.dataset.filter] = i.checked);
  return on;
}

function renderList() {
  const on = activeFilters();
  const q = document.getElementById("search").value.trim().toLowerCase();
  const list = document.getElementById("entry-list");
  const nodes = [];
  let module = null;
  for (const e of state.entries) {
    if (!on[kindGroup(e.kind)]) continue;
    if (e.aux && !on.aux) continue;
    if (q && !(e.name.toLowerCase().includes(q) || e.text.toLowerCase().includes(q))) continue;
    if (e.module !== module) {
      module = e.module;
      nodes.push(el("div", { class: "module-head" }, module));
    }
    const stmt = (e.premises.length ? e.premises.join(", ") + " ⊢ " : "") + e.text;
    nodes.push(el("button", {
      class: "entry-item" + (e.k === state.selectedK ? " selected" : ""),
      "data-k": e.k,
      onclick: () => showEntry(e.k),
    },
      el("div", { class: "name" }, el("span", { class: "badge " + e.kind }, KIND_LABELS[e.kind] || e.kind), e.name),
      el("div", { class: "stmt" }, stmt)));
  }
  if (!nodes.length) nodes.push(el("p", { class: "placeholder", style: "padding: 12px" }, "該当するエントリはありません。"));
  list.replaceChildren(...nodes);
}

// --- one entry ----------------------------------------------------------------------

function parseHash() {
  const m = location.hash.match(/^#([\w-]+)(?:\/(\d+))?$/);
  return m ? { world: m[1], k: m[2] ? Number(m[2]) : null } : null;
}

async function showEntry(k) {
  state.selectedK = k;
  history.replaceState(null, "", `#${state.world}/${k}`);
  document.querySelectorAll(".entry-item").forEach(b => {
    const on = Number(b.dataset.k) === k;
    b.classList.toggle("selected", on);
    if (on) b.scrollIntoView({ block: "nearest" });
  });
  const detail = document.getElementById("entry-detail");
  let e;
  try {
    e = await api(`/api/entry?world=${encodeURIComponent(state.world)}&k=${k}`);
  } catch (err) {
    detail.replaceChildren(el("p", { class: "placeholder" }, "読み込めませんでした: " + err.message));
    return;
  }
  const premises = e.premiseFormulas.map(formulaNode);
  const statement = el("div", { class: "statement" },
    premises.length ? [...joinNodes(premises, ", "), el("span", { class: "turnstile" }, "⊢")] : null,
    formulaNode(e.conclusion));
  const parts = [
    el("h1", {}, e.name),
    el("div", { class: "meta" },
      el("span", { class: "badge " + e.kind }, KIND_LABELS[e.kind] || e.kind),
      el("code", {}, e.module), `　#${e.k}　起源: ${e.origin}`),
    statement,
    el("pre", { class: "sexp" }, e.conclusion.sexp),
  ];
  if (e.discharged) {
    parts.push(el("p", { class: "muted" }, "演繹定理で仮定 ", el("span", { style: "font-family: var(--math)" }, formulaNode(e.discharged)), " を含意の前件に移した定理です。",
      e.expanded ? "移した後の証明も実際の推論図として組み立て、検証済みです。"
                 : "体系が宣言した演繹定理の規則を信頼して登録しています。"));
  }
  parts.push(...dependencySections(e));
  if (e.conditions.length) {
    parts.push(el("div", { class: "section-title" }, "側条件"),
      el("div", { class: "conditions" }, ...e.conditions.map(c => el("div", {}, c))));
  }
  if (e.proof) {
    const holder = el("div");
    let mode = "tree";
    const switcher = el("span", { class: "view-switch" },
      el("button", { "data-mode": "table" }, "表"),
      el("button", { "data-mode": "tree", class: "active" }, "証明図"));
    const draw = () => {
      switcher.querySelectorAll("button").forEach(b => b.classList.toggle("active", b.dataset.mode === mode));
      holder.replaceChildren(mode === "table" ? proofTable(e.proof) : proofTree(e.proof));
    };
    switcher.addEventListener("click", ev => { if (ev.target.dataset.mode) { mode = ev.target.dataset.mode; draw(); } });
    parts.push(
      el("div", { class: "section-title" }, `証明（${e.proof.length} 行）`, switcher,
        STATIC ? copyButton(e.proofSexp)
               : el("button", { class: "secondary", onclick: () => openInEditor(e.proofSexp) }, "エディタで開く")),
      holder);
    draw();
  } else if (["axiom", "irule", "wff?", "term?", "var?"].includes(e.kind)) {
    parts.push(el("p", { class: "muted" }, "無条件に信頼される基本エントリ（.system ファイル由来）です。?x などはスキーマ変数です。"));
  }
  detail.replaceChildren(...parts);
  detail.scrollTop = 0;
}

// --- what an entry rests on, and what uses it -------------------------------------

function refList(refs) {
  return el("ul", { class: "ref-list" }, ...refs.map(r =>
    el("li", {},
      entryLink(r.k, r.name, { class: "link ref-name", title: `#${r.k} を新しいタブで開く` }),
      el("span", { class: "ref-text" }, r.text))));
}

function groupByModule(refs) {
  const groups = new Map();
  for (const r of refs) {
    if (!groups.has(r.module)) groups.set(r.module, []);
    groups.get(r.module).push(r);
  }
  return [...groups].flatMap(([module, rs]) => [el("div", { class: "ref-module" }, module), refList(rs)]);
}

function dependencySections(e) {
  const out = [];
  const f = e.foundations;
  if (f && (e.hasProof || f.definitions.length)) {
    const body = [];
    if (f.axioms.length) body.push(el("div", { class: "dep-sub" }, `公理（${f.axioms.length}）`), ...groupByModule(f.axioms));
    if (f.definitions.length) body.push(el("div", { class: "dep-sub" }, `定義（${f.definitions.length}）`), refList(f.definitions));
    if (f.rules.length) {
      body.push(el("div", { class: "dep-sub" }, "推論規則"),
        el("p", { class: "inline-refs" }, ...joinNodes(f.rules.map(r =>
          entryLink(r.k, r.name, { class: "link", title: r.text })), "、")));
    }
    if (f.deductionMeta) {
      body.push(el("p", { class: "trust-note" },
        "途中で、演繹定理の規則を（推論図に展開せずに）信頼して登録した定理（th-ded）を使っています。"));
    }
    out.push(el("details", { class: "deps", open: "" },
      el("summary", {}, "この" + (e.hasProof ? "定理" : "エントリ") + "が依存している基礎"),
      ...body));
  }
  if (e.usedBy.length || e.dependents) {
    out.push(el("details", { class: "deps", open: e.usedBy.length <= 12 ? "" : null },
      el("summary", {}, `このエントリを使っている定理　直接 ${e.usedBy.length} 件・間接を含め ${e.dependents} 件`),
      el("p", { class: "muted small" }, "途中の補題（名前.t5、名前-s1 など）から使われている場合は、その補題を使っている定理として数えています。"),
      refList(e.usedBy)));
  } else if (["axiom", "irule", "th", "th-ded"].includes(e.kind)) {
    out.push(el("p", { class: "muted small" }, "このエントリを使っている定理は、まだありません。"));
  }
  return out;
}

function citeLink(line) {
  const text = [line.rule, ...line.args].filter(Boolean).join(" ");
  if (line.cite && line.cite.k) {
    return entryLink(line.cite.k, text, { class: "link", title: `引用している #${line.cite.k} を新しいタブで開く` });
  }
  return text;
}

// --- proof as a table -----------------------------------------------------------------

function proofTable(lines) {
  const rows = new Map();
  const table = el("table", { class: "proof" });
  for (const line of lines) {
    const refs = line.refs.map(r => el("span", {
      class: "ref",
      onmouseenter: () => rows.get(r)?.classList.add("hl"),
      onmouseleave: () => rows.get(r)?.classList.remove("hl"),
    }, r));
    const why = line.role === "hyp"
      ? "仮定"
      : [ROLE_LABELS[line.role] || line.role, " ", citeLink({ ...line, args: line.args.filter(a => !line.refs.includes(a)) })];
    const tr = el("tr", { class: line.status || "" },
      el("td", { class: "n" }, line.n),
      el("td", { class: "f", title: line.formula.sexp }, formulaNode(line.formula)),
      el("td", { class: "why" }, why, refs.length ? ["　← ", ...refs.flatMap((r, i) => i ? [", ", r] : [r])] : null));
    rows.set(line.n, tr);
    table.append(tr);
  }
  return table;
}

// --- proof as a tree ----------------------------------------------------------------------
// Each proof line is a node; the lines it cites are drawn above a horizontal
// bar, the rule that justifies it to the right of the bar. A Hilbert proof is
// a DAG, so a line cited twice appears twice. Click a bar to fold/unfold.

function proofTree(lines) {
  const byN = new Map(lines.map(l => [l.n, l]));
  const root = lines[lines.length - 1];
  const wrap = el("div", { class: "tree-wrap" });
  // small proofs open fully; large ones start with the last two steps
  const initialDepth = lines.length <= 12 ? 99 : 2;
  wrap.append(treeNode(root, byN, 0, new Set(), initialDepth));
  // the root's conclusion sits at the horizontal centre of a wide tree;
  // start scrolled there so the final result is visible first
  requestAnimationFrame(() => { wrap.scrollLeft = (wrap.scrollWidth - wrap.clientWidth) / 2; });
  return el("div", {},
    el("p", { class: "tree-hint" }, "横線をクリックすると、その上の部分を折りたたみ／展開できます。規則名や式の中の記号をクリックすると、引用先・導入元のエントリが新しいタブで開きます。"),
    wrap);
}

function treeNode(line, byN, depth, path, initialDepth) {
  const node = el("div", { class: "pnode " + (line.status || "") });
  const concl = el("div", { class: "concl" + (line.role === "hyp" ? " hyp" : ""), title: `${line.n}: ${line.formula.sexp}` }, formulaNode(line.formula));
  if (line.role === "hyp") {
    node.append(concl);
    return node;
  }
  const premises = el("div", { class: "premises" });
  const label = el("span", { class: "label" }, citeLink({ ...line, args: line.args.filter(a => !line.refs.includes(a)) }));
  const barRow = el("div", { class: "bar-row" }, el("div", { class: "bar" }), label);
  let open = depth < initialDepth;
  const children = line.refs.map(r => byN.get(r)).filter(Boolean);
  const fill = () => {
    barRow.classList.toggle("collapsed", !open && children.length > 0);
    if (!children.length) { premises.replaceChildren(); return; }
    if (!open) { premises.replaceChildren(el("span", { class: "elided", title: "クリックで展開" }, "⋮")); return; }
    const next = new Set(path).add(line.n);
    premises.replaceChildren(...children.map(c =>
      next.has(c.n) ? el("span", { class: "elided" }, `(${c.n})`) : treeNode(c, byN, depth + 1, next, initialDepth)));
  };
  barRow.addEventListener("click", ev => {
    if (ev.target.closest("a, button")) return;   // links navigate instead
    open = !open;
    fill();
  });
  fill();
  node.append(premises, barRow, concl);
  return node;
}

// In the static site: copy the proof's S-expression instead of opening the editor.
function copyButton(text) {
  const b = el("button", { class: "secondary", title: "証明の S 式をクリップボードへ" }, "S式をコピー");
  b.addEventListener("click", async () => {
    try { await navigator.clipboard.writeText(text); b.textContent = "コピーしました"; }
    catch { b.textContent = "コピーできません"; }
    setTimeout(() => { b.textContent = "S式をコピー"; }, 1500);
  });
  return b;
}

// The static site's landing text, in place of "pick an entry".
// The landing text shown until an entry is picked.
function intro() {
  const worlds = (state.worlds || []).map(w => `${w.title}（${w.entries} エントリ）`).join("、");
  const mode = STATIC
    ? "これは静的に書き出した閲覧専用の版です。書き出しの時点で、すべての証明をカーネルが最初から検証し直しています"
      + `（${STATIC.generated}${STATIC.revision ? "、commit " + STATIC.revision : ""}）。`
      + "新しい証明の検証は、サーバー版のエディタで行えます。"
    : "上の「エディタ」タブで証明を書くと、選んでいる体系の台帳に対してその場で検証されます（台帳には追加されません）。"
      + "定理のページの「エディタで開く」で、その証明を編集して試せます。";
  return el("div", { class: "static-intro" },
    el("h1", {}, "Ledger Kernel"),
    el("p", {}, "追記専用の台帳（ledger）で「証明可能」を管理する、Hilbert 流の証明検証系のライブラリです。"
      + "左の一覧から公理・定理を選ぶと、命題・証明（表と証明図）・依存している公理・その定理を使っている定理を見られます。"
      + "式の記号や規則名をクリックすると、導入元・引用先のエントリが新しいタブで開きます。"),
    worlds ? el("p", {}, "収録：" + worlds + "。") : null,
    el("p", { class: "muted small" }, mode),
    el("p", { class: "muted small" },
      "AI の支援を受けて作成した実験的なソフトウェアで、第三者による監査は受けていません。"));
}

// --- editor ---------------------------------------------------------------------------

function openInEditor(proofText) {
  document.getElementById("proof-input").value = proofText;
  switchView("editor");
  runCheck();
}

async function runCheck() {
  const summary = document.getElementById("check-summary");
  const out = document.getElementById("check-result");
  summary.className = "summary muted";
  summary.textContent = "検証中…";
  let r;
  try {
    r = await api("/api/check", {
      method: "POST",
      headers: { "Content-Type": "application/json; charset=utf-8" },
      body: JSON.stringify({ world: state.world, proof: document.getElementById("proof-input").value }),
    });
  } catch (err) {
    summary.className = "summary bad";
    summary.replaceChildren(el("span", { class: "verdict" }, "エラー"), err.message);
    out.replaceChildren();
    return;
  }
  state.lastCheck = r;
  const sequent = r.conclusion
    ? el("span", { class: "sequent" },
        ...(r.hypotheses.length ? [...joinNodes(r.hypotheses.map(formulaNode), ", "), " "] : []),
        "⊢ ", formulaNode(r.conclusion))
    : null;
  if (r.ok) {
    summary.className = "summary ok";
    summary.replaceChildren(el("span", { class: "verdict" }, "✓ 検証成功"), `全 ${r.lines.length} 行が受理されました。`, sequent);
  } else {
    summary.className = "summary bad";
    const why = r.error ? r.error : `${r.failedAt} 行目が受理されませんでした（それより前の行は受理、後の行は未検証）。`;
    summary.replaceChildren(el("span", { class: "verdict" }, "✗ 検証失敗"), why, r.ok === false && r.conclusion ? sequent : null);
  }
  drawCheck();
}

function drawCheck() {
  const out = document.getElementById("check-result");
  const r = state.lastCheck;
  if (!r || !r.lines.length) { out.replaceChildren(); return; }
  out.replaceChildren(state.editorMode === "table" ? proofTable(r.lines) : proofTree(r.lines));
}

// --- wiring -------------------------------------------------------------------------------

function switchView(name) {
  document.querySelectorAll(".tab").forEach(t => t.classList.toggle("active", t.dataset.view === name));
  document.querySelectorAll(".view").forEach(v => v.classList.toggle("active", v.id === "view-" + name));
}

document.querySelectorAll(".tab").forEach(t => t.addEventListener("click", () => switchView(t.dataset.view)));
document.getElementById("search").addEventListener("input", renderList);
document.querySelectorAll(".filters input").forEach(i => i.addEventListener("change", renderList));
document.getElementById("check-btn").addEventListener("click", runCheck);
document.getElementById("proof-input").addEventListener("keydown", ev => {
  if (ev.key === "Enter" && (ev.ctrlKey || ev.metaKey)) { ev.preventDefault(); runCheck(); }
});
document.getElementById("editor-switch").addEventListener("click", ev => {
  const mode = ev.target.dataset.mode;
  if (!mode) return;
  state.editorMode = mode;
  document.querySelectorAll("#editor-switch button").forEach(b => b.classList.toggle("active", b.dataset.mode === mode));
  drawCheck();
});

// Following an entry link in the same tab (e.g. the browser's back button)
window.addEventListener("hashchange", async () => {
  const h = parseHash();
  if (!h) return;
  if (h.world !== state.world) {
    state.world = h.world;
    document.getElementById("world").value = h.world;
    await loadEntries();
  }
  if (h.k && h.k !== state.selectedK) { switchView("library"); showEntry(h.k); }
});

// The static site has no kernel behind it: no editor tab.
if (STATIC) document.querySelector('.tab[data-view="editor"]').hidden = true;

loadWorlds().catch(err => {
  document.getElementById("entry-detail").replaceChildren(el("p", { class: "placeholder" }, "サーバーに接続できません: " + err.message));
});
