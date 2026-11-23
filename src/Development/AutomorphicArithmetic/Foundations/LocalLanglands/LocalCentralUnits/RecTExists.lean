module

public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CuspLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneCharpolyTwistSpecial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ArtEx
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.CuspEx
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.RecTTransport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConductorRecCompatible
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsTameWeilDeligneIffWildCharpolyStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDim
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.CharZeroAdicCompletion
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsReadingLaws
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDim
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDual
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivProdIrrZero
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZero
import Mathlib.Data.Nat.Choose.Multinomial
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Mathlib.Tactic.ReduceModChar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEqStatement
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.GoodSeg
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RcTwOfSegments
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.TypeIff
public import Development.DiscreteGroups.GlobalIrreducibility.DzLCusp

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LanglandsExtensionUniqueOnCuspidal

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LangExt

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  haveI : LeftCommutative (WD.lpSum (h := h)) :=
    ⟨fun a b c => by rw [← WD.lpSum_assoc, WD.lpSum_comm a b, WD.lpSum_assoc]⟩
  exact hp.foldr_eq _

theorem charZero_adicCompletion : CharZero (w.adicCompletion E) :=
  charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective

end GlobalTheory.LocLanglands.LangExt


open GlobalTheory.LocLanglands.LangExt in
theorem GlobalTheory.LocLanglands.exists_isLExt : LanglandsExhaustionGL → LanglandsMultisegments → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (r : IrrGL (k := w.adicCompletion E) → WD h), (∃ rc, IsLExt r rc) ∧ ∀ rc, IsLExt r rc → ∀ x : IrrGL (k := w.adicCompletion E), x.IsCusp → rc x = r x := by
  intro hX hM E Ω _ _ _ _ _ A w h r
  haveI : CharZero (w.adicCompletion E) := LangExt.charZero_adicCompletion
  refine ⟨⟨fun x => segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList, ?_⟩, ?_⟩
  · intro l x hl
    have hm := Classical.choose_spec (hX (w.adicCompletion E) x)
    have he := (hM (w.adicCompletion E)).1 _ _ x hm hl
    show segSum r (Classical.choose (hX (w.adicCompletion E) x)).toList = segSum r l
    unfold segSum
    apply LangExt.sumList_perm
    apply List.Perm.map
    apply Multiset.coe_eq_coe.1
    rw [Multiset.coe_toList]
    exact he
  · intro rc hrc x hx
    have h1 := hrc [.single x hx] x (single_spec hx).2.2.2
    rw [h1]
    change (((r x).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp (h := h) 1)).lpSum (WD.lpZero (h := h)) = r x
    rw [WD.lpSum_zero]
    have h2 := (GlobalTheory.WeilDeligne.charPol_lpTw_lpChar_lpSp E Ω A w h (r x)).1
    have h3 : ((((1 : ℕ) : ℝ) - 1) / 2) = 0 := by norm_num
    rw [h3]
    exact h2

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtDepth

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extDepth :
    UpperTheory.Zero.LLC.ExtDepth := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hext x hgood hdz
  rw [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly]
  intro σ hσ
  obtain ⟨⟨hdim, s, hsup, hcusp, hchar⟩, -⟩ := UpperTheory.Zero.LLC.extDim E Ω A w h a ha r rc hr hext x
  obtain ⟨s0, hsup0, hgc⟩ := hgood
  have hs : s0 = s := (UpperTheory.Zero.LLC.goodSeg _).2.2 x s0 s hsup0 hsup
  subst hs
  have hdzy : ∀ y ∈ s0, UpperTheory.Zero.LLC.DZ y := by
    obtain ⟨m, f, hf, hcs⟩ := hsup
    intro y hy
    rw [← hf] at hy
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp hy
    have key := UpperTheory.Zero.LLC.Pr.dzs _ x.fst (GlobalTheory.SplitRead.Irr.ofIrrRep x.snd.rep) m (fun i => (f i).fst)
      (fun i => GlobalTheory.SplitRead.Irr.ofIrrRep (f i).snd.rep) hcs ((Submodule.ne_bot_iff _).mp hdz) i
    exact (Submodule.ne_bot_iff _).mpr key
  have htame : ∀ y ∈ s0, (r y).charPol σ = (X - 1) ^ y.fst := by
    intro y hy
    have hy' := hr.depth y (hcusp y hy) (hgc y hy) (hdzy y hy)
    rw [GlobalTheory.T.isTameWeilDeligne_iff_wild_charpoly] at hy'
    rw [hy' σ hσ, hr.dim y (hcusp y hy)]
  rw [hchar σ, Multiset.map_congr rfl htame, GlobalTheory.LlcDepth.prod_map_pow (X - 1) Sigma.fst s0,
    HasSupport.sum_fst hsup, Fintype.card_fin, hdim]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivProdChosenIrrGLPairDegreeZeroStatement

section

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

theorem _root_.GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (x z : IrrGL (k := k)) (hz : z.1 = 0) (hd : ∑ a, (![x, z] a).1 = x.1), Nonempty (x.rep.Equiv (prodIrr ![x, z] hd)) := by
  first | exact @GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero | exact GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero | (intros; apply GlobalTheory.LocGL.nonempty_equiv_prodIrr_pair_zero <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsExtensionInjective

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocLanglands.LExtInj

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_irreducible_GL_zero : ∃ t : IrrGL (k := k), t.1 = 0 ∧ IsL (0 : Multiset (Segment k)) t.rep :=
  ⟨IrrGL.of (detRep (Fin 0) (1 : kˣ →* ℂˣ)) ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar)
    (isIrreducible_ofChar _), rfl, (Tests.empty_spec (k := k)).2.of_equiv (IrrGL.equivOf _ _ _)⟩

theorem sum_fst_of_lFactors' {𝔪 : Multiset (Segment k)} {c : ℕ} {x : Fin c → IrrGL (k := k)} (hx : LFactors 𝔪 x) :
    ∑ a, (x a).1 = (𝔪.map Segment.deg).sum := by
  obtain ⟨Δ, ⟨rfl, -⟩, hΔ⟩ := hx
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  exact Finset.sum_congr rfl fun a _ => (hΔ a).deg_eq.symm

theorem deg_of_isL' {V : Type} [AddCommGroup V] [Module ℂ V] {N : ℕ} {𝔪 : Multiset (Segment k)}
    {π : Representation ℂ (GL (Fin N) k) V} (h : IsL 𝔪 π) : (𝔪.map Segment.deg).sum = N := by
  obtain ⟨_, x, hd, hx, -⟩ := h
  exact (sum_fst_of_lFactors' hx).symm.trans hd

theorem eq_of_isL (hM : LanglandsMultisegments) [CharZero k] (𝔪 : Multiset (Segment k)) (x y : IrrGL (k := k))
    (hx : IsL 𝔪 x.rep) (hy : IsL 𝔪 y.rep) : x = y := by
  obtain ⟨t, ht0, ht⟩ := exists_irreducible_GL_zero (k := k)
  have hdeg : x.1 = y.1 := (deg_of_isL' hx).symm.trans (deg_of_isL' hy)
  obtain ⟨nx, cx⟩ := x
  obtain ⟨ny, cy⟩ := y
  obtain rfl : nx = ny := hdeg
  have hd : ∑ a, (![(⟨nx, cx⟩ : IrrGL (k := k)), t] a).1 = nx := by simp [Fin.sum_univ_two, ht0]
  have hs := (hM k).2 𝔪 0 ![⟨nx, cx⟩, t] ⟨nx, cy⟩ hd hx ht (by rwa [add_zero])
  obtain ⟨φ⟩ := GlobalTheory.T.nonempty_equiv_prodChosenIrrGL_pair_degreeZero k (⟨nx, cx⟩ : IrrGL (k := k)) t ht0 hd
  have hs2 : IsSubquotient (IrrGL.rep (⟨nx, cy⟩ : IrrGL (k := k))) (IrrGL.rep (⟨nx, cx⟩ : IrrGL (k := k))) :=
    hs.trans (.of_injective φ.symm.toIntertwiningMap φ.symm.toLinearEquiv.injective)
  obtain ⟨ψ⟩ := hs2.nonempty_equiv cy.rep.irr cx.rep.irr
  congr 1
  rw [← cx.cl_rep, ← cy.cl_rep]
  exact IrrRep.cl_eq_iff.2 ⟨ψ⟩

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem isIrrWD_lpTw {y : WD h} (hy : IsIrrWD y) (s : ℝ) : IsIrrWD (y.lpTw s) := by
  obtain ⟨n, a, rfl, ha⟩ := hy
  exact ⟨n, a.tw s, (WD.lpTw_mk a s).symm, isIrreducible_twist ha _⟩

theorem lpTw_injective {y y' : WD h} {s : ℝ} (e : y.lpTw s = y'.lpTw s) : y = y' := by
  have := congrArg (fun z : WD h => z.lpTw (-s)) e
  simpa only [WD.lpTw_add, add_neg_cancel, WD.lpTw_zero] using this

end GlobalTheory.LocLanglands.LExtInj

end
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.ExtInj

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.extInj :
    UpperTheory.Zero.LLC.ExtInj := by
  intro E Ω _ _ _ _ _ A w h a ha r rc hr hL x y hy hxy
  classical
  obtain ⟨mx, hmx⟩ := UpperTheory.Zero.LLC.Pr.exh _ x
  obtain ⟨my, hmy⟩ := UpperTheory.Zero.LLC.Pr.exh _ y
  have hlx : IsL (↑mx.toList) x.rep := by rw [Multiset.coe_toList]; exact hmx
  have hly : IsL (↑my.toList) y.rep := by rw [Multiset.coe_toList]; exact hmy
  have hgood : ∀ Δ ∈ my.toList, UpperTheory.Zero.LLC.GoodCusp Δ.first :=
    ((UpperTheory.Zero.LLC.goodSeg _).1 _ y hly).1 hy
  have e := hxy
  rw [hL _ x hlx, hL _ y hly] at e
  let f : Segment (HeightOneSpectrum.adicCompletion E w) → WD h × ℕ :=
    fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2), Δ.len - 1)
  have hcomp : (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp (h := h) (p.2 + 1))) ∘ f =
      fun Δ => ((r Δ.first).lpTw ((↑Δ.len - 1) / 2)).lpChar (WD.lpSp (h := h) Δ.len) := by
    funext Δ
    simp only [Function.comp, f, Nat.sub_add_cancel Δ.len_pos]
  have hirr : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)), ∀ p ∈ l.map f, IsIrrWD p.1 := by
    intro l p hp
    obtain ⟨Δ, -, rfl⟩ := List.mem_map.mp hp
    exact LExtInj.isIrrWD_lpTw (hr.irr _ (Segment.isCusp_first _)) _
  have hperm := GlobalTheory.T.perm_of_weilDeligne_special_decomposition_eq E Ω A w h (mx.toList.map f) (my.toList.map f) (hirr _) (hirr _)
    (by rw [List.map_map, List.map_map, hcomp]; exact e)
  have key : ∀ Δ Δ' : Segment (HeightOneSpectrum.adicCompletion E w),
      UpperTheory.Zero.LLC.GoodCusp Δ'.first → f Δ = f Δ' → Δ = Δ' := by
    intro Δ Δ' hg he
    simp only [f, Prod.mk.injEq] at he
    obtain ⟨h1, h2⟩ := he
    have hl : Δ.len = Δ'.len := by
      have := Δ.len_pos
      have := Δ'.len_pos
      omega
    rw [hl] at h1
    exact Segment.ext_first
      (hr.inj _ _ (Segment.isCusp_first _) (Segment.isCusp_first _) hg (LExtInj.lpTw_injective h1)) hl
  let g : WD h × ℕ → Option (Segment (HeightOneSpectrum.adicCompletion E w)) := fun p =>
    if hp : ∃ Δ ∈ my.toList, f Δ = p then some hp.choose else none
  have hgy : ∀ Δ ∈ my.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    have hp : ∃ Δ' ∈ my.toList, f Δ' = f Δ := ⟨Δ, hΔ, rfl⟩
    simp only [g, dif_pos hp]
    exact congrArg some (key _ _ (hgood Δ hΔ) hp.choose_spec.2)
  have hgx : ∀ Δ ∈ mx.toList, g (f Δ) = some Δ := by
    intro Δ hΔ
    obtain ⟨Δ', hΔ', he⟩ := List.mem_map.mp (hperm.subset (List.mem_map_of_mem hΔ))
    have := key Δ Δ' (hgood Δ' hΔ') he.symm
    subst this
    exact hgy _ hΔ'
  have back : ∀ l : List (Segment (HeightOneSpectrum.adicCompletion E w)),
      (∀ Δ ∈ l, g (f Δ) = some Δ) → (l.map f).filterMap g = l := by
    intro l hl
    induction l with
    | nil => rfl
    | cons b t ih =>
      rw [List.map_cons, List.filterMap_cons_some (hl b List.mem_cons_self)]
      exact congrArg _ (ih fun Δ hΔ => hl Δ (List.mem_cons_of_mem _ hΔ))
  have hp2 : mx.toList.Perm my.toList := by
    have := hperm.filterMap g
    rwa [back _ hgx, back _ hgy] at this
  have hmm : (↑mx.toList : Multiset (Segment (HeightOneSpectrum.adicCompletion E w))) = ↑my.toList :=
    Multiset.coe_eq_coe.mpr hp2
  rw [hmm] at hlx
  exact LExtInj.eq_of_isL UpperTheory.Zero.LLC.Pr.multi _ x y hlx hly
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.LocalLanglands.LocalCentralUnits.RecTExists

section

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Zero.LLC.recTExists :
    UpperTheory.Zero.LLC.RecTExists := by
  intro E Ω _ _ _ _ _ A w h
  obtain ⟨a, ha, -⟩ := UpperTheory.Zero.LLC.artEx E Ω A w h
  obtain ⟨r, hr⟩ := UpperTheory.Zero.LLC.cuspEx E Ω A w h a ha
  obtain ⟨⟨rc, hrc⟩, hcu⟩ :=
    GlobalTheory.LocLanglands.exists_isLExt UpperTheory.Zero.LLC.Pr.exh UpperTheory.Zero.LLC.Pr.multi E Ω A w h r
  have hcusp : ∀ x : IrrGL (k := HeightOneSpectrum.adicCompletion E w), x.IsCusp → rc x = r x :=
    hcu rc hrc
  have hD := UpperTheory.Zero.LLC.extDim E Ω A w h a ha r rc hr hrc
  have hT := UpperTheory.Zero.LLC.extTw E Ω A w h a ha r rc hr hrc
  refine ⟨rc, a, ha, ?_⟩
  refine
    { dim := fun x => (hD x).1.1
      one := fun χ hχ => (hcusp _ (IrrGL.isCusp_ofChar χ hχ)).trans (hr.one χ hχ)
      langlands := ?_
      cusp := ?_
      nu := hT.1
      absCentral := fun x ω hω σ => ((hD x).2 ω hω σ).1
      twist := ?_
      central := fun x ω hg hω σ => ((hD x).2 ω hω σ).2 hg
      dual := UpperTheory.Zero.LLC.extDual E Ω A w h a ha r rc hr hrc
      inj := UpperTheory.Zero.LLC.extInj E Ω A w h a ha r rc hr hrc
      depth := fun x hg hx => UpperTheory.Zero.LLC.extDepth E Ω A w h a ha r rc hr hrc x hg hx
      type := ?_ }
  · intro l x hl
    rw [hrc l x hl]
    unfold GlobalTheory.LocLanglands.segSum
    congr 1
    refine List.map_congr_left ?_
    intro Δ _
    rw [hcusp _ Δ.isCusp_first]
  · intro x hx
    rw [hcusp x hx]
    exact hr.irr x hx
  · intro x χ hχ hg
    rw [hcusp _ (IrrGL.isCusp_ofChar χ hχ), hr.one χ hχ]
    exact hT.2 x χ hχ hg
  · refine (UpperTheory.Zero.LLC.typeIff E Ω A w h rc).2 ?_
    intro x
    unfold UpperTheory.Zero.LLC.TypeAt
    intro g _ i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
    have hx : x.IsCusp := by
      subst hσ
      exact IrrGL.isCusp_of.2 ⟨hn, DiscreteGroups.sglob.DzLc.isCuspidal_of_inflates i hi τ hτ σ hinf⟩
    rw [hcusp x hx]
    exact hr.type x hx g i hi n hn D R hR θ hθ τ hτ hN σ hσ hinf
end
end
