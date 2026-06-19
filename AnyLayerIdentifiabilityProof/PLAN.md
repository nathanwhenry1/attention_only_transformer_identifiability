# Plan & remaining work

What is left to formalize, tracked **against the natural-language proof
`n_layer_proof.tex`** (Lean source root). For the map of what exists and where, see
**`ARCHITECTURE.md`**. These are the only two docs.

**THE PROOF IS COMPLETE (2026-06-18).** Zero sorries; the whole library builds green and the
public theorem `TransformerIdentifiability.identifiability` is **axiom-clean**
(`#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorryAx`). The analytic crux
`dial_mem` (`Step2/RealizedTailMatching.lean`) and the final R5 step-3b wiring (§Wiring) are both
done. The TeX lemma reproductions below (with full proofs) document the discharged `dial_mem` math
and remain as reference. _Work landed on branch `wiring`; baseline `master` is the restore point._

## Snapshot

- **Zero `sorry`.** The last one (`texGenericMainCurrentConstructorProvider`,
  `IdentifiabilityProof.lean`) was closed by collapsing the realized-tail leaf record
  `TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData` to a single
  `matching : FirstLayerMatchedData θ θ'` field, produced genuinely by
  `realizedTailMatchedData_of_uniformTailRealize` (`Step2/RealizedTailMatching.lean`) via the leaf
  value `idlReducedRealizedTailMatchingFrecProvider_genuine` (`IdentifiabilityMain.lean`). The
  sorry was filled with
  `texGenericMainThreadedCurrentConstructorProvider_of_builderSelectedTailLeaves` applied to that
  leaf (PUnit at depths 0/1).
- The genuine matching pipeline (`Step2/RealizedTailMatching.lean`, axiom-clean): parking-trick
  `dial_mem` (reduces to `D.O ⊆ Uprev` = `subset_rfl` since each node has `Uprev = D.O`) → genuine
  `TexFirstLayerMatchingAnalyticDataOfTrichotomy` →
  `realizedTailMatchedData_of_uniformTailRealize : FirstLayerMatchedData θ θ'`. Because
  `FirstLayerMatchedData` is a **Prop**, the record change is proof-irrelevance-safe; the legacy
  `IDLRecursiveAnalyticData` Sigma uses `Σ'`/PSigma for its `matching` component. The clean route
  avoided the ~94-reference fake-`T` obligation retype.
- Axiom audit: public `identifiability` = `[propext, Classical.choice, Quot.sound]` — the three
  standard Lean axioms only. No `sorryAx`, no project-specific axioms anywhere in the tree.
- Depths 0–1 vacuous, depth 2 independently complete; the depth ≥ 3 inductive step of `thm:IDL`
  (below) is fully discharged.

## Build & audit commands

From the **repo root** (parent of `AnyLayerIdentifiabilityProof/`), with
`export PATH="/nas/ucb/nathanhenry/.elan/bin:$PATH"`. Host `rnn` is a shared Slurm login —
keep builds targeted; lake rejects `-j`/`--jobs` short forms.

- Full: `lake build AnyLayerIdentifiabilityProof.identifiability` · one module:
  `lake build AnyLayerIdentifiabilityProof.NLayer.Step2.IDLMatching` · one file:
  `lake env lean <path>.lean`
- Audit: `rg -n '\b(sorry|admit|axiom)\b' AnyLayerIdentifiabilityProof`; per-name
  `#print axioms <name>` (clean = `[propext, Classical.choice, Quot.sound]`).
- Git: first commit is baseline `master` (clean, green, one sorry); endgame work is on branch
  **`wiring`**, `master` is the restore point. Commit after each verified-green milestone.
  `.gitignore` excludes `/.lake`. Iterate the endgame on the small top module
  `lake build AnyLayerIdentifiabilityProof.NLayer.Step2.RealizedTailMatching` (~10s).

## Already discharged (orientation only — do not re-derive)

- **Step 1** (`prop:A1`, `cor:depth`): `A₁=A₁'`, `V₁≠0` — via the `A_gp` global-product route.
- **Step 2** (`prop:trichotomy`, `prop:matching`): `V₁=V₁'`, `B₁=B₁'`, and
  `closedRecursionLimits` — genuine trichotomy at `IDLMatching.lean:3159`; limits producer landed
  this session.
- **Step 3 engine**: `UniformTailRealize` induction (`Step2/SweepRealization.lean`) and
  `texSweepCanonicalIFTData_of_IDLData_matching_realizedTail` (`Step2/SweepWiring.lean:464`) —
  proved; `canonicalIFT` is free at a realized-tail node.
- **`dial_mem` (this session)**: the realized-tail dial membership is proved in
  `Step2/RealizedTailMatching.lean` (axiom-clean) via the *parking trick* — the dial converges
  to its base (`tendsto_dialPathData_probe`), so feeding the parent invariant `hprev :
  UniformTailRealize …` a path that follows the dial after its entry time and sits at the base
  before it realizes the dial; the only hypothesis is `D.O ⊆ Uprev` (`subset_rfl`, since the
  threaded recursion sets each node's `Uprev = D.O`). Both the local-patch and the raw
  trichotomy-explicit forms are provided.
- **§8 genericity** (`prop:genericnonempty`, `prop:anchorsexist`): exact bad set is null
  (`mainTheoremExceptionalSet_null`); anchors exist.

All math engines are proved. What remains is feeding them into the leaf (the R5 wiring, §Wiring).

---

## Reference (DISCHARGED): the `dial_mem` math

> **Status: done.** This section is retained as reference for the math now proved in
> `Step2/RealizedTailMatching.lean`. The Lean route ended up *simpler* than a literal
> transcription: rather than re-running the holomorphic realization per dial, the parent's
> already-built `UniformTailRealize` invariant is reused via the **parking trick** (the dial
> converges to its base by `lem:dial`(c); a path that follows the dial past its entry time and
> sits at the base before it is confined to the parent region everywhere, so the parent
> invariant realizes it and its realizer agrees with the dial asymptotically). The faithful
> paper content that survives is `n_layer_proof.tex:648`'s endpoint definition of `𝒫(𝒪)`,
> realized as the inclusion `N.Uq ⊆ D.O` (`texMatchingProductNeighborhood_Uq_subset_O`).

### The Lean obligation

At a recursive node `D.Paths = realizedTailPathSet r θfull FullPaths`. `dial_mem`
(`TexMatchingLocalPatchRegularQuadricDialMemObligation`) asks: **every canonical
regular-quadric dial path is the realized r-tail of some source path in `FullPaths`, with a
`RealizationData` witness** (`DescentIDL.lean`). Equivalently (sweep side): the canonical
anchor lies in the parent's IFT region, so the previous realization neighborhood transports
forward. The paper proves this via **dial path → Realization → Sweep**; the Lean proof
realizes it via the parking trick above. Full TeX transcription follows (reference).

### Background objects and identities

First-layer scalars (common to `θ`, `θ'` after Steps 1–2; `B₁ = I + V₁`):
`q(w,v) = wᵀA₁v`, `π(w,v) = A₁ᵀw − A₁v`, and (from `n_layer_proof.tex` 2580–2594)

```latex
\Phi_t(w,v):=\big((B_1-tV_1)w,\ B_1v+tV_1w\big),\qquad
\vartheta_0(w,v,t):=\pi(w,v)^\top(B_1-tV_1)^{-1}V_1w
```

(the latter wherever `det(B₁−tV₁)≠0`). The **first-layer effective path** of `P=(w,v)∈𝒞_T` is
`τ ↦ ((B₁−s₁(τ)V₁)w(τ), B₁v(τ)+s₁(τ)V₁w(τ))` with `s₁(τ)=σ(τ·q(w(τ),v(τ))+b)`, `b=log r`.

The probe reduction (`prop:probe`) turns a probe input into the 2D recursion
`wℓ=(Bℓ−sℓVℓ)w_{ℓ−1}`, `vℓ=Bℓv_{ℓ−1}+sℓVℓw_{ℓ−1}`, `sℓ=σ(τλℓ+b)`,
`λℓ=w_{ℓ−1}ᵀAℓv_{ℓ−1}`, observable `F⁽ᴸ⁾=v_L`. The peeling identity makes the recursion one
layer at a time:

```latex
\begin{lemma}[Peeling]\label{lem:peeling}
For every $\theta$, $(w,v)\in\R^{2d}$, $\tau>0$, with $s_1=\sig(\tau\,w^\top A_1v+b)$,
\[ F^{(L)}_\theta(w,v,\tau)=F^{(L-1)}_{\theta_{\ge2}}\big((B_1-s_1V_1)w,\;B_1v+s_1V_1w,\;\tau\big). \]
\end{lemma}
\begin{proof}
By Proposition~\ref{prop:probe} ($\ell=1$), the hidden state after the first layer is
$X^{(1)}=\sqrt\tau\,[\,u_1\cdots u_1\ v_1\,]$ with $\lambda_1=w^\top A_1v$,
$s_1=\sig(\tau\lambda_1+b)$, $w_1=(B_1-s_1V_1)w$, $v_1=B_1v+s_1V_1w$, $u_1=B_1(w+v)$. The
probe form is preserved: $w_1+v_1=B_1(w+v)=u_1$, so $X^{(1)}=X_{w_1,v_1}(\tau)$. Since
$\TF_\theta=\TF_{\theta_{\ge2}}\circ\mathrm{Layer}_{V_1,A_1}$,
$\TF_\theta(X_{w,v}(\tau))=\TF_{\theta_{\ge2}}(X_{w_1,v_1}(\tau))$; applying
Proposition~\ref{prop:probe} to $\theta_{\ge2}$ and reading off the last column gives
$F^{(L)}_\theta(w,v,\tau)=F^{(L-1)}_{\theta_{\ge2}}(w_1,v_1,\tau)$.
\end{proof}
```

→ Lean: peeling is what makes "realized r-tail" precise; `realizedTailPathSet` is `r` peelings
of a source path. `θ_{≥2}` is the Lean `tail`.

### `lem:dial` — the paths `dial_mem` quantifies over (statement + proof)

```latex
\begin{lemma}[Dial paths]\label{lem:dial}
Let $(w^0,v^0,t)\in\cU$. Set $\pi^0:=\pi(w^0,v^0)\neq0$, $c:=\logit t-b$,
$y:=\pi^0/|\pi^0|^2$, and define the dial path $P_{w^0,v^0,t}=(w,v)$,
$w(\tau):=w^0-\tfrac{c}{\tau}y$, $v(\tau):=v^0+\tfrac{c}{\tau}y$. Then:
(a) $u(\tau):=w(\tau)+v(\tau)\equiv w^0+v^0$; $P\in\cH_{T_0}$ for every $T_0>0$, with
$P(\infty)=(w^0,v^0)\in\cO$; hence $P\in\cP(\cO)$.
(b) With $\hat\rho:=y^\top A_1y$: $\tau q(w(\tau),v(\tau))+b=\logit t-c^2\hat\rho/\tau$.
(c) for real $\tau>0$, $s_1(\tau)\in(0,1)$ and $|s_1(\tau)-t|\le C/\tau$ ($C:=\tfrac14c^2|\hat\rho|$),
so $s_1(\tau)\to t$ and $(w(\tau),v(\tau))\to(w^0,v^0)$.
(d) all of (b)–(c) hold for the primed parameter, since $A_1=A_1'$; in particular $s_1'=s_1$ along $P$.
\end{lemma}
\begin{proof}
(a) The sum is constant (perturbations cancel). Each component of $w,v$ is $a+b'/\tau$,
holomorphic and bounded on $\{|\tau|>T_0\}$, real for real $\tau$; the limit at $\infty$ is
$(w^0,v^0)\in\cO$ by Lemma~\ref{lem:region}(ii). Hence $P\in\cH_{T_0}$, $P\in\cP(\cO)$.
(b) Using $q(w^0,v^0)=0$ and bilinearity, with $a:=c/\tau$:
$q(w(\tau),v(\tau))=a\,y^\top(A_1^\top w^0-A_1v^0)-a^2\hat\rho=a\,y^\top\pi^0-a^2\hat\rho=a-a^2\hat\rho$
(since $y^\top\pi^0=1$). Multiply by $\tau$, add $b$: $\tau q+b=\logit t-(c^2/\tau)\hat\rho$.
(c) For real $\tau>0$ the $\sig$ argument is real, so $s_1\in(0,1)$; with $|\sig'|\le\tfrac14$
and $t=\sig(\logit t)$, the MVT on (b) gives $|s_1(\tau)-t|\le\tfrac14c^2|\hat\rho|/\tau$.
(d) all quantities are built from $A_1,b$ and base data; $A_1'=A_1$ so the first gate coincides.
\end{proof}
```

→ Lean: `texMatchingRegularQuadricDialPathData signRegion T N p hp t ht`. (c) is the `s₁→t`
"dial"; `𝒰` (the connected sign region with (i)–(iii)) is the node's `SignRegionData` /
`TexRegionConstructionData` (already built). `lem:region(ii)` ("base ∈ 𝒪") is what `dial_mem`
must upgrade to "base path ∈ `FullPaths` as a realized tail".

### `lem:realization` — the heart of `dial_mem` (statement + full proof)

```latex
\begin{lemma}[Realization]\label{lem:realization}
Let $(w^0,v^0)\in\R^{2d}$ and $t\in(0,1)$ satisfy $q(w^0,v^0)=0$, $\pi^0:=\pi(w^0,v^0)\neq0$,
$V_1w^0\neq0$, $\det(B_1-tV_1)\neq0$, $\vartheta_0(w^0,v^0,t)\neq0$. Let
$\widetilde P=(\widetilde w,\widetilde v)\in\cH_{T_0}$ with $\widetilde P(\infty)=\Phi_t(w^0,v^0)$.
Then there exist $T\ge T_0$ and $P=(w,v)\in\cH_T$ with $P(\infty)=(w^0,v^0)$ such that for real $\tau>T$,
$(B_1-s_1(\tau)V_1)w(\tau)=\widetilde w(\tau)$, $B_1v(\tau)+s_1(\tau)V_1w(\tau)=\widetilde v(\tau)$,
where $s_1(\tau)=\sig(\tau q(w(\tau),v(\tau))+b)$. I.e. the first-layer effective path of $P$ equals $\widetilde P$.
\end{lemma}
\begin{proof}
Write $\vartheta_0:=\vartheta_0(w^0,v^0,t)\neq0$, $c:=\logit t-b$. A scalar Banach fixed point in the first gate's dial value.

\emph{Step 0 (real symmetry).} Call $f$ holomorphic on $\{|\tau|>T'\}$ real-symmetric if
$\overline{f(\bar\tau)}=f(\tau)$. Members of $\cH_{T'}$ are real-symmetric: $g(\tau):=\overline{f(\bar\tau)}$
is holomorphic on the same (connected) set and $=f$ on $(T',\infty)$, so $g\equiv f$ by the
identity theorem; extensions to $\infty$ inherit it. Applied componentwise to vectors.

\emph{Step 1 (auxiliary family $v_S$).} Since $\det B_1\neq0$ ((G3)), set
$u(\tau):=B_1^{-1}(\widetilde w(\tau)+\widetilde v(\tau))$, holomorphic/bounded/real-symmetric,
with $u(\infty)=w^0+v^0=:u^0$. Set $M:=(B_1-tV_1)^{-1}V_1$, $\varsigma_*:=\tfrac1{2(1+\|M\|)}>0$.
For $|S-t|<\varsigma_*$, $B_1-SV_1=(B_1-tV_1)(I-(S-t)M)$ is invertible (Neumann series), and
$S\mapsto(B_1-SV_1)^{-1}$ is holomorphic on $D(t,\varsigma_*)$ with real Taylor coefficients at $t$. Define
$v_S(\tau):=(B_1-SV_1)^{-1}(\widetilde v(\tau)-S\,V_1u(\tau))$, i.e. $V(\zeta,S):=v_S(1/\zeta)$
jointly holomorphic on $D(0,1/T_0)\times D(t,\varsigma_*)$. The exact identity
\[ B_1v_S(\tau)+S\,V_1(u(\tau)-v_S(\tau))=\widetilde v(\tau) \tag{vSident} \]
holds. Anchor values: $v_t(\infty)=v^0$, and $\mu:=\partial_Sv_S|_{(\infty,t)}=-(B_1-tV_1)^{-1}V_1w^0$.
\emph{Claim (real symmetry of $V$):} $\overline{V(\bar\zeta,\bar S)}=V(\zeta,S)$ — by the identity
theorem first in $\zeta$ for real $S$, then in $S$.

\emph{Step 2 (scalar data).} Define $Q(\tau,\varsigma):=q(u(\tau)-v_{t+\varsigma}(\tau),\,v_{t+\varsigma}(\tau))$,
$\widehat Q(\zeta,\varsigma):=Q(1/\zeta,\varsigma)$, jointly holomorphic, real-symmetric. Anchors:
$\widehat Q(0,0)=q(w^0,v^0)=0$ and, by bilinearity and $\mu$,
$\partial_\varsigma\widehat Q(0,0)=\pi^{0\top}\mu=-\pi^{0\top}(B_1-tV_1)^{-1}V_1w^0=-\vartheta_0\neq0$.
Pick $\delta_1\le\tfrac1{2T_0}$, $\varsigma_1\le\tfrac14\min(\varsigma_*,t,1-t)$. Divided difference
\[ \widehat\cR(\zeta,\varsigma):=\frac1{2\pi i}\oint_{|\omega|=3\varsigma_1}
   \frac{\widehat Q(\zeta,\omega)}{(\omega-\varsigma)\,\omega}\,d\omega, \]
jointly holomorphic, with $\varsigma\widehat\cR=\widehat Q(\cdot,\varsigma)-\widehat Q(\cdot,0)$,
$\widehat\cR(\zeta,0)=\partial_\varsigma\widehat Q(\zeta,0)$, $\widehat\cR(0,0)=-\vartheta_0$,
real-symmetric. With $a_0(\zeta):=\widehat Q(\zeta,0)$, $a_0(0)=0$ (here $q(w^0,v^0)=0$ is consumed),
so $\widehat h(\zeta):=a_0(\zeta)/\zeta$ extends holomorphically (removable), $\widehat h(1/\tau)=\tau Q(\tau,0)$;
$H_\infty:=\sup_{|\zeta|\le\delta_1}|\widehat h|$. And $\psi(\varsigma):=(\logit(t+\varsigma)-\logit t)/\varsigma$
extends holomorphically with real coefficients, $C_\psi:=\sup_{|\varsigma|\le\varsigma_1}|\psi|$.
Shrink $\delta_1,\varsigma_1$ so $|\widehat\cR|\ge\tfrac12|\vartheta_0|$ on
$\bar P:=\overline{D(0,\delta_1)}\times\overline{D(0,2\varsigma_1)}$. Define
$F(\zeta,\varsigma):=\dfrac{c-\widehat h(\zeta)+\varsigma\psi(\varsigma)}{\widehat\cR(\zeta,\varsigma)}$,
$M_F:=\sup_{\bar P}|F|$, with Cauchy estimate $|\partial_\varsigma F|\le M_F/\varsigma_1=:L_F$, so
$|F(\zeta,a)-F(\zeta,b)|\le L_F|a-b|$.

\emph{Step 3 (fixed point).} Let $\rho:=\max(1,\tfrac4{|\vartheta_0|}(|c|+H_\infty))$ and
$T:=\max\{\tfrac1{\delta_1},\tfrac{\rho}{\varsigma_1},\tfrac{4C_\psi}{|\vartheta_0|},2L_F\}\ge T_0$.
Let $\widehat X_T$ be bounded holomorphic functions on $A_T:=\{|\tau|>T\}$ (sup norm, complete),
$\bar B_\rho$ the closed $\rho$-ball, and $\cT(x)(\tau):=F(1/\tau,\,x(\tau)/\tau)$. Well defined on
$A_T$ (arguments stay in $\bar P$). \emph{Self-map:} $|\cT(x)|\le\tfrac{|c|+H_\infty+C_\psi\rho/T}{\tfrac12|\vartheta_0|}\le\rho$.
\emph{Contraction:} $|\cT(x)-\cT(y)|\le\tfrac{L_F}{T}\|x-y\|\le\tfrac12\|x-y\|$. Banach gives a unique
fixed point $x^*\in\bar B_\rho$; \emph{reality:} $x^\dagger(\tau):=\overline{x^*(\bar\tau)}$ is also a
fixed point (real symmetry of $F$), so $x^*=x^\dagger$ is real-symmetric, real on $(T,\infty)$.

\emph{Step 4 (gate consistency).} Put $S(\tau):=t+x^*(\tau)/\tau$; $|S-t|\le\rho/T\le\varsigma_1<\min(t,1-t)$,
so $S(\tau)\in(0,1)$ for real $\tau>T$. Multiplying $x^*=F(1/\tau,x^*/\tau)$ by $\widehat\cR$ and using
$\varsigma\widehat\cR=\widehat Q(\cdot,\varsigma)-\widehat Q(\cdot,0)$, $\widehat h(1/\tau)=\tau Q(\tau,0)$,
and $\logit(t+\varsigma)=\logit t+\varsigma\psi(\varsigma)$ gives
\[ \logit S(\tau)-b=\tau\,Q(\tau,\,x^*(\tau)/\tau)\qquad(\text{real }\tau>T). \tag{fixed} \]

\emph{Step 5 (assembling the path).} Define $v(\tau):=v_{S(\tau)}(\tau)=V(1/\tau,S(\tau))$,
$w(\tau):=u(\tau)-v(\tau)$. Both holomorphic, bounded, real on $(T,\infty)$, so $P=(w,v)\in\cH_T$;
$S(\tau)\to t$ gives $v(\tau)\to v^0$, $w(\tau)\to w^0$, i.e. $P(\infty)=(w^0,v^0)$. For real $\tau>T$,
$Q(\tau,x^*/\tau)=q(w(\tau),v(\tau))$, so (fixed) reads $\logit S(\tau)-b=\tau q(w,v)$, i.e.
$S(\tau)=\sig(\tau q(w,v)+b)=s_1(\tau)$. Then (vSident) at $S=s_1(\tau)$ gives
$B_1v+s_1V_1w=\widetilde v$, and $(B_1-s_1V_1)w=B_1u-(B_1v+s_1V_1w)=(\widetilde w+\widetilde v)-\widetilde v=\widetilde w$.

\emph{Closing remarks.} (i) $\pi^0\neq0$, $V_1w^0\neq0$ follow from $\vartheta_0\neq0$. (ii) $A_1$
invertibility is unused. (iii) $\det B_1\neq0$ ((G3)) is used once, defining $u$.
\end{proof}
```

→ Lean: **this is the `RealizationData` witness** (`DescentIDL.lean`) and the content of
`Step2/SweepRealization.lean`'s pointwise realization (already built abstractly). Given a target
tail path `P̃` with `P̃(∞)=Φ_t(w⁰,v⁰)`, it returns a source path `P` (`P(∞)=(w⁰,v⁰)`) whose
first-layer effective path is `P̃`. Hypotheses (`q=0`, `π≠0`, `V₁w⁰≠0`, `det(B₁−tV₁)≠0`, `ϑ₀≠0`)
are the genericity/region facts the node carries (`endpoint` + `SignRegionData`). `dial_mem` =
"this applies to the canonical dial points of this node, and the resulting `P` lies in `FullPaths`."

### `lem:sweep` — the open region / re-anchoring (statement + full proof)

```latex
\begin{lemma}[Sweep]\label{lem:sweep}
Let the first layer be common with $\det B_1\neq0$, $(w^\sharp,v^\sharp)\in\cQ$ with
$\pi(w^\sharp,v^\sharp)\neq0$, $t_\sharp\in(0,1)$ with $\det(B_1-t_\sharp V_1)\neq0$,
$\vartheta_0(w^\sharp,v^\sharp,t_\sharp)\neq0$, and $(w^\sharp,v^\sharp)\in\cO$ open. Then there are a
relatively open $N\subseteq\cQ\times(0,1)$ containing $(w^\sharp,v^\sharp,t_\sharp)$ and an open
$\widetilde\cO\ni p^\flat:=\Phi_{t_\sharp}(w^\sharp,v^\sharp)$ such that
\[ \text{every }(w,v,t)\in N:\ (w,v)\in\cO,\ q=0,\ \pi\neq0,\ V_1w\neq0,\ \det(B_1-tV_1)\neq0,\ \vartheta_0\neq0; \tag{persist} \]
and $\widetilde\cO\subseteq\Psi(N)$, $\Psi(w,v,t):=\Phi_t(w,v)$.
\end{lemma}
\begin{proof}
\emph{Step 0 (persistence).} $\vartheta_0(w^\sharp,v^\sharp,t_\sharp)\neq0$ forces $V_1w^\sharp\neq0$,
$\pi(w^\sharp,v^\sharp)\neq0$. Each quantity in (persist) is continuous and nonzero (or the membership
open) at the point, so there is a relatively open $N_0\subseteq\cQ\times(0,1)$ on which (persist) holds
($q=0$ on all of $\cQ\times(0,1)$).
\emph{Step 1 (chart).} $\nabla q(w^\sharp,v^\sharp)=(A_1v^\sharp,A_1^\top w^\sharp)\neq0$ (else
$\pi=0$). By the IFT for $q$, there are open $\Xi\subseteq\R^{2d-1}$, $\xi^\sharp$, and a real-analytic
homeomorphism $\gamma:\Xi\to\cQ$ onto a relative neighbourhood of $(w^\sharp,v^\sharp)$,
$\gamma(\xi^\sharp)=(w^\sharp,v^\sharp)$, $\mathrm{im}\,D\gamma(\xi^\sharp)=\cT:=\ker\nabla q^\top$.
\emph{Step 2 (Jacobian + inverse function theorem).} Define $G(\xi,t):=\Phi_t(\gamma(\xi))$. Its
differential at $(\xi^\sharp,t_\sharp)$ has the $2d-1$ columns $\Phi_{t_\sharp}(D\gamma(\xi^\sharp)e_i)$
plus the $t$-column $\partial_t\Phi_t|_{t_\sharp}=(-V_1w^\sharp,V_1w^\sharp)$. The linear $\Phi_{t_\sharp}$
is block-triangular with $\det=\det(B_1-t_\sharp V_1)\det B_1\neq0$, an isomorphism; so $DG$ is invertible
iff $h:=\Phi_{t_\sharp}^{-1}(-V_1w^\sharp,V_1w^\sharp)\notin\cT$. Computing $h=(-m,m)$ with
$m:=(B_1-t_\sharp V_1)^{-1}V_1w^\sharp$,
\[ \nabla q(w^\sharp,v^\sharp)\cdot h=m^\top(A_1^\top w^\sharp-A_1v^\sharp)
   =\pi(w^\sharp,v^\sharp)^\top(B_1-t_\sharp V_1)^{-1}V_1w^\sharp=\vartheta_0(w^\sharp,v^\sharp,t_\sharp)\neq0, \]
so $h\notin\cT$, $DG(\xi^\sharp,t_\sharp)$ invertible. By the inverse function theorem, shrinking to
$\Xi'\times J'$, $G$ is a diffeomorphism onto an open $\widetilde\cO\ni p^\flat$; shrinking so
$N:=\gamma(\Xi')\times J'\subseteq N_0$ (so (persist) holds, $N$ relatively open), every point of
$\widetilde\cO$ is $G(\xi,t)=\Psi(\gamma(\xi),t)$, i.e. $\widetilde\cO\subseteq\Psi(N)$.
\end{proof}
```

→ Lean: `TexSweepCanonicalIFTData` (= near-anchor local realization), produced by
`texSweepCanonicalIFTData_of_IDLData_matching_realizedTail` (`SweepWiring.lean:464`). `Õ` becomes the
child's `Uprev`; (persist) is the bundle of region facts licensing `lem:realization` on `N`. The open
residual is that the child node's canonical anchor sits in this `Õ` (`(idlChosenFullAnchor D).1 ∈ Uprev`)
— the membership half of `dial_mem`. Note the key computation `∇q·h = ϑ₀ ≠ 0` is exactly why `ϑ₀≠0`
is the right nondegeneracy.

### The induction that consumes them — `thm:IDL`, inductive step `L≥2`

```latex
(1) By Prop.~\ref{prop:A1}, Cor.~\ref{cor:depth}, Prop.~\ref{prop:matching}: $A_1=A_1'$, $V_1=V_1'(\neq0)$,
$B_1=B_1'$; by (G3) $\det B_1\neq0$. $q,\pi,\Phi_t,\vartheta_0$ coincide for both parameters.
(2) By the anchor clause of (SH), fix $(w^\sharp,v^\sharp)\in\cO\cap\cM_L(\theta')$, and by (M3) a
$t_\sharp\in(0,1)$ with $\det(B_1-t_\sharp V_1)\neq0$, $\vartheta_0(w^\sharp,v^\sharp,t_\sharp)\neq0$,
$p^\flat:=\Phi_{t_\sharp}(w^\sharp,v^\sharp)\in\cM_{L-1}(\theta'_{\ge2})$. By (M1) $q(w^\sharp,v^\sharp)=0$, $\pi\neq0$.
(3) Lemma~\ref{lem:sweep} gives relatively open $N$ (with (persist), $N\subseteq\{(w,v)\in\cO\}$) and open
$\widetilde\cO\ni p^\flat$, $\widetilde\cO\subseteq\Psi(N)$. Then $\widetilde\cO\cap\cM_{L-1}(\theta'_{\ge2})\ni p^\flat$:
the anchor clause at depth $L-1$ is re-established.
(4) Let $\widetilde P\in\cP(\widetilde\cO)$, $\widetilde p:=\widetilde P(\infty)\in\widetilde\cO$. By (3),
$\widetilde p=\Phi_t(w^0,v^0)$ for some $(w^0,v^0,t)\in N$; by (persist), Lemma~\ref{lem:realization}
applies, producing $P\in\cP(\cO)$ whose first-layer effective path is $\widetilde P$. Since first layers
coincide, $s_1$ is shared, and Lemma~\ref{lem:peeling} gives
$G^P_\theta=G^{\widetilde P}_{\theta_{\ge2}}$, $G^P_{\theta'}=G^{\widetilde P}_{\theta'_{\ge2}}$ on $(T,\infty)$;
with (SH) ($G^P_\theta=G^P_{\theta'}$), $G^{\widetilde P}_{\theta_{\ge2}}=G^{\widetilde P}_{\theta'_{\ge2}}$ eventually.
(5) $(\theta'_{\ge2},\theta_{\ge2},\widetilde\cO)$ satisfy the depth-$(L-1)$ hypotheses
($\theta'_{\ge2}\in\cG^{(L-1)}$, $\widetilde\cO$ open nonempty, anchor clause by (3), agreement by (4)).
By induction $\theta_{\ge2}=\theta'_{\ge2}$; with (1), $\theta=\theta'$.
```

→ Lean: the recursion the leaf feeds. The realized-tail node = "depth `L−1` on `Õ`". `dial_mem` is
step (4) ("every `P̃∈𝒫(Õ)` is realized by a `P∈𝒫(𝒪)`") restricted to the canonical dial paths.
**Filling `dial_mem` is transcribing (2)→(4): pick the (M3) `t♯`; invoke the built sweep for `N`/`Õ`;
invoke the built realization on each dial; package the source path + `RealizationData`.**

### The anchor and its transport — `def:anchor` (M1–M3), `lem:unwind`

```latex
\cM_1:=\R^{2d}; for $m\ge2$, $(w,v)\in\cM_m(\vartheta)$ iff
(M1) $q(w,v)=0$, $A_1^\top w\neq0$, $\pi(w,v)\neq0$;
(M2) $\exists s\in(0,1)$: $\phi^\vartheta_\ell(s,1,\dots,1;w,v)>0$, $\ell=2,\dots,m$;
(M3) $\exists t\in(0,1)$: $\det(B_1-tV_1)\neq0$, $\pi(w,v)^\top(B_1-tV_1)^{-1}V_1w\neq0$,
     and $\Phi^\vartheta_t(w,v)\in\cM_{m-1}(\vartheta_{\ge2})$.
```

`lem:unwind` (TeX 3122) expands `𝓜_L` into a level-by-level system `(a)–(d)` for `k=0..L−2` (slope
vanishing/positivity, `(A'_{k+1})ᵀw_{(k)}≠0`, the determinant/`ϑ₀`-type nonvanishing), by induction over
parameters. → Lean: (M3)'s `Φ_t` is the transport carrying the anchor one layer deeper. The
**anchor-threading fix**: define the child node's canonical anchor as `Φ_{t♯}` of the parent's, so it lands
in `Õ=Uprev` by construction — discharging the membership residual in move (4).

### → Lean dictionary

| TeX | Lean |
|---|---|
| `q,π,Φ_t,ϑ₀`; first layer common (`A₁=A₁'`,`V₁=V₁'`,`det B₁≠0`) | node region data; `endpoint : FirstLayerEndpointData` |
| `𝒞_{T₀}`, `𝒫(𝒪)` | `ProbePath d`; `FullPaths`; node `D.Paths = realizedTailPathSet r θfull FullPaths` |
| dial path `P_{w⁰,v⁰,t}` | `texMatchingRegularQuadricDialPathData …` |
| effective path / `lem:peeling` | the r-fold realized tail (`realizedTailPathSet`) |
| `lem:realization` output | `RealizationData` (`DescentIDL.lean`); `Step2/SweepRealization.lean` (built) |
| `lem:sweep` `Õ`,`N`,(persist) | `TexSweepCanonicalIFTData`/`Uprev`; produced at `SweepWiring.lean:464` |
| induction (2)–(4) | the content of `dial_mem` at a recursive node |
| (M3) `Φ_t` transport | anchor-threading (`(idlChosenFullAnchor D).1 ∈ Uprev`) |
| genuine trichotomy / `prop:matching` limits | `closedRecursionLimits` producer (done this session) |

---

## Wiring (R5) — the remaining work, with a clean route

The leaf's reduced record (`TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData`,
`IdentifiabilityMain.lean:567`) is typed against the **local-patch obligations**, whose internal
trichotomy is the **fake `varsigma≡1`** `texTrichotomyConstructionData_of_signRegion`
(`IDLMatching.lean:4415`). The genuine `closedRecursionLimits` producer outputs the **genuine**
trichotomy `texTrichotomyConstructionData_of_inductionProvider`. An *in-place* retype of those
obligations would thread `hd : 2 ≤ d` + genuine `T` through ~94 references — avoid this.

**Clean route (the plan):** the **univ node already matches via the genuine trichotomy**, *not* the
fake-`T` chain — `firstLayerMatched_of_texGenericStep_of_IDLData_trichotomy` (`IDLMatching.lean:16823`)
consumes a `TexFirstLayerMatchingAnalyticDataOfTrichotomy` (`:16753`) that carries its **own genuine
`T`**. The only Paths-specific input to its producer (16881, the univ builder) is the raw dial
membership `hdial_mem`, fed into `texMatchingDialPathLimitBridgeData_of_regularQuadricLimit`. So the
realized-tail leaf can **reuse this exact path**, supplying *our* `dial_mem` where the univ node
supplies `texMatchingRegularQuadricDialMemObligation_of_paths_univ`. The fake-`T` local-patch
obligations stay untouched (unused on the realized-tail path) — no ~94-ref retype.

## Suggested work order

1. **(DONE)** `dial_mem` math + the raw trichotomy-explicit producer
   `texMatchingRegularQuadricDialMemObligation_of_uniformTailRealize_of_region_subset`
   (`Step2/RealizedTailMatching.lean`) — the realized-tail analogue of the univ node's
   `_of_paths_univ` dial membership, valid for the genuine `T`.
2. **(DONE)** genuine matching-analytic producers
   `texFirstLayerMatchingAnalyticDataOfTrichotomy_of_{cascadeBuilder,inductionProvider}_dialMem`
   (`RealizedTailMatching.lean`) — mirror `IDLMatching.lean:16881/17059` but take `hdial_mem` instead
   of `_of_paths_univ`, yielding `TexFirstLayerMatchingAnalyticDataOfTrichotomy` at genuine `T`.
3. **(DONE, "3a")** `realizedTailMatchedData_of_uniformTailRealize`
   (`RealizedTailMatching.lean`) — the full genuine-matching builder: from `(hstep, endpoint, D,
   signRegion, hPaths, Uprev, Tprev, hprev, D.O ⊆ Uprev)` it builds the genuine `P/T/N/S/actual`
   (Paths-independent, per the univ build `IdentifiabilityMain.lean:5244-5285`), feeds our `dial_mem`
   to the bridge, and returns `FirstLayerMatchedData θ θ'` via `firstLayerMatched_…_trichotomy`.
   The entire genuine matching pipeline now lives in `RealizedTailMatching.lean`, all axiom-clean.
4. **(REMAINING — "3b", the closing refactor)** in `IdentifiabilityMain.lean`:
   - change the record `TexMatchingReducedRealizedTailLocalPatchRegularQuadricFrecProviderData`
     (`:567`) from its two fake-`T` fields to a single `matching : FirstLayerMatchedData θ θ'`
     (a thin wrapper; the recursive-data structures `:1176`/`:1377` keep their `matchingFrec` field
     of this record type, so they don't change);
   - `import …Step2.RealizedTailMatching`; fill the leaf provider (which the `sorry` provides) with
     `{ matching := realizedTailMatchedData_of_uniformTailRealize … }` (it has `hstep/endpoint`,
     builds `localRegion→region→signRegion`, and carries `Uprev/hprev/(D.O ⊆ Uprev)`);
   - rewire **every** consumer that rebuilds `matching` from the record via the fake-`T` chain
     (`reducedRealizedTailMatchingProviderData_to_frecProviderData` + the closed-recursion sibling —
     **~7 sites**, not 2: ≈ `:801, :888, :1411, :1457, :1557, :1671, :1819, :1863, :1998` in the
     pre-edit file) to `let matching := <record>.matching`; **delete** the now-dead helper defs
     (`…_of_dialMem_closedRecursionLimits` / `…_of_realizedTailMemData_…` / `…_of_realizedTailMemObligation_…`,
     `reducedRealizedTailMatchingProviderData_to_frecProviderData`,
     `closedRecursionLimitObligation_of_reducedRealizedTailMatchingProviderData`);
   - **fill the `sorry`** (`IdentifiabilityProof.lean:1037`) via
     `texGenericMainThreadedCurrentConstructorProvider_of_builderSelectedTailLeaves` applied to the
     leaf provider (PUnit at depths 0/1).
   Do it compiler-guided: change the record, build `IdentifiabilityMain` (~32s) to enumerate every
   broken site, fix each. Final check: `#print axioms identifiability` must drop `sorryAx`.
   (An earlier attempt under-scoped this as a 2-site change and was reverted to green; the record
   change + the `:1457`/`:1671` rewires are correct and re-doable verbatim.)

## Working notes

- **Big files** (slow rebuild): `Step2/IDLMatching` (~17.8k), `IDL/IDLStep1` & `Step2/IDLSweep` (~7.7–9k),
  `IdentifiabilityMain` (~5.6k). Navigate by signature.
- **New top module `Step2/RealizedTailMatching.lean` (created this session)** imports
  `Step2/IDLMatching` + `Step2/SweepRealization` and holds the **entire genuine matching pipeline**
  (all axiom-clean): the `dial_mem` parking-trick bridges + `texMatchingProductNeighborhood_Uq_subset_O`,
  the raw trichotomy-explicit dial-membership producer, the genuine analytic-data producers
  (`…_of_{cascadeBuilder,inductionProvider}_dialMem`), and `realizedTailMatchedData_of_uniformTailRealize`
  (→ `FirstLayerMatchedData`). It is a small **top** module, so its edit/rebuild loop is ~10s vs.
  recompiling `IDLMatching` (~17.8k lines). Only the final 3b rewire touches `IdentifiabilityMain`.
  The clean route (see §Wiring) means the in-place fake-`T` retype of `IDLMatching` is **not**
  needed — those obligations stay whole. Stable files (`IDLStep1`, `IDLSweep`, `IdentifiabilityMain`)
  left whole until the proof closes; post-proof they can be split along `/-!` section headers.
- **Two parallel cascade developments:** the proof uses the **integrated** route in `Step2/IDLMatching`
  (`…productPatchZeroBranch`); the separate `IDL/Cascade*.lean` files are an additive R1/R2/R3 development
  **not yet imported**. Don't assume they're wired in.
- **Banked analytic lemmas** (`Analytic/{WeierstrassClosed,ExteriorConnected,DividedDifference}`): the
  holomorphic-realization route was dropped for the pointwise scalar-IFT route — not needed. (Note the
  realization proof above *is* complex-analytic, but the Lean engine `SweepRealization.lean` realizes it
  pointwise; the banked files are an alternative not on the path.)
- **Aggregators** `NLayer.lean`, `NLayer/Step1.lean` — import-only.
- **Ignore** off-path files: `AnyLayerIdentifiabilityProof/{2_layer_identifiability,TwoLayerIdentifiability,Basic}.lean`,
  repo-root `2_layer_*`, `1_layer_proof.tex`, `proof.tex`.
- Several `.lean` doc-comments still cite the old (now-deleted) planning docs by name; harmless.
