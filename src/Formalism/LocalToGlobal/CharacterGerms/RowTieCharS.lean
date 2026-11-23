module

public import Formalism.LocalToGlobal.CharacterGerms.MfactMulCoeffMvExpLinF
public import Formalism.LocalToGlobal.CharacterGerms.RowTieChar
public import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
public import Formalism.DropLevelBounds.ConstantCoeffVanishing.UbintConstantCoeffEqZero
public import Formalism.LocalToGlobal.CharacterGerms.AbstractGermZeroCondition
public import Formalism.LocalToGlobal.CharacterGerms.RowTieFB
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
import Formalism.LocalToGlobal.CharacterGerms.SubstSubst
import Formalism.LocalToGlobal.ProjectiveLattices.SubConstMemOrig
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.CMField
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
public import Formalism.LocalToGlobal.CharacterGerms.ValuationEqPairOfUnitGerm
public import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero
import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffSinglePointZero
public import Formalism.LocalToGlobal.CharacterGerms.IntSProd
import Formalism.LocalToGlobal.CharacterGerms.RowTieCartAdd
public import Formalism.LocalToGlobal.CharacterGerms.UncurryLogConstantCoeff
public import Formalism.LocalToGlobal.CharacterGerms.GeneralGermZero

-- Source module: Formalism.LocalToGlobal.CharacterGerms.ChartHypothesisOfCharacters

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

open VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I : Fin 2 → Type} [∀ g, Fintype (I g)]

theorem integralSeries_uncurry_one {χ : PS C 1 dd} (h : IntS V χ) : IntS V (un1 χ) := by
  intro μ
  exact h _

end ChG


section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.ConstantCoeffPderivUncurry

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ChG

section Uniq

variable {K : Type} [Field K] [CharZero K] {τ : Type} [Fintype τ]

theorem exp_unique (y : τ → K) (Ψ : MvPowerSeries τ K) (h0 : MvPowerSeries.constantCoeff Ψ = 1)
    (hd : ∀ w, MvPowerSeries.pderiv (R := K) w Ψ = Ψ * MvPowerSeries.C (y w)) : Ψ = mvExp (linF y) := by
  have step : ∀ (w : τ) (m : τ →₀ ℕ), MvPowerSeries.coeff (m + Finsupp.single w 1) Ψ * ((m w : K) + 1) =
      y w * MvPowerSeries.coeff m Ψ := by
    intro w m
    have h := congrArg (MvPowerSeries.coeff m) (hd w)
    rw [MvPowerSeries.coeff_pderiv, mul_comm Ψ, MvPowerSeries.coeff_C_mul] at h
    exact h
  have key : ∀ (n : ℕ) (m : τ →₀ ℕ), m.degree = n →
      MvPowerSeries.coeff m Ψ = MvPowerSeries.coeff m (mvExp (linF y)) := by
    intro n
    induction n with
    | zero =>
      intro m hm
      have hm0 : m = 0 := (Finsupp.degree_eq_zero_iff m).1 hm
      subst hm0
      rw [coeff_zero_mvExp, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h0]
    | succ n ih =>
      intro m hm
      obtain ⟨w, hw⟩ : ∃ w, m w ≠ 0 := by
        by_contra hcon
        simp only [not_exists, not_not] at hcon
        have : m = 0 := Finsupp.ext hcon
        rw [this] at hm
        simp at hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + Finsupp.single w 1 := by
        refine ⟨m - Finsupp.single w 1, ?_⟩
        ext x
        by_cases hx : x = w
        · subst hx
          simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_eq_same]
          omega
        · simp [Ne.symm hx]
      have hdeg : m'.degree = n := by
        rw [map_add (f := _), Finsupp.degree_single] at hm
        omega
      have hne : ((m' w : K) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m' w)
      have e1 := step w m'
      have e2 := coeff_mvExp_linF_step y w m'
      rw [ih m' hdeg, ← e2] at e1
      exact mul_right_cancel₀ hne e1
  ext m
  exact key _ m rfl

end Uniq

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}
  (Y : FBChart C V O dd)

open VP

theorem chi_mul {χ : PS C 1 dd} (hχ : Y.IsChar χ) :
    MvPowerSeries.subst (fun k => Y.B.G.F k) (un1 χ) =
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ) *
        MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd)) (un1 χ) := by
  have h := hχ.2.2
  rw [eval_single_eq_subst, eval_single_eq_subst, eval_single_eq_subst] at h
  rw [subst_singlePointUncurry (cc_F Y), subst_singlePointUncurry (fun _ => cc_X _), subst_singlePointUncurry (fun _ => cc_X _)]
  have h2 : (fun p : Fin 1 × Fin dd => addOf Y.B.G.F (pt C dd 0) (pt C dd 1) p.2) =
      fun p : Fin 1 × Fin dd => Y.B.G.F p.2 := by
    funext p
    exact ev_id _
  rw [h2] at h
  exact h

theorem constantCoeff_pderiv_uncurry (χ : PS C 1 dd) (i : Fin dd) :
    MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (R := C) i (un1 χ)) = dlogC χ i := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  have h1 : MvPowerSeries.coeff (Finsupp.single i 1) (un1 χ) = dlogC χ i := by
    show MvPowerSeries.coeff ((Finsupp.single i 1).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) χ = _
    rw [Finsupp.mapDomain_single]
    rfl
  simp [h1]

def Psi (χ : PS C 1 dd) : MvPowerSeries (Fin dd) C := MvPowerSeries.subst (e Y) (un1 χ)

theorem chi_ode {χ : PS C 1 dd} (hχ : Y.IsChar χ) (i : Fin dd) :
    MvPowerSeries.pderiv (R := C) i (Psi Y χ) = Psi Y χ * MvPowerSeries.C (dlogC χ i) := by
  have hFK : ∀ k, Y.B.FK C k = Y.B.G.F k := by
    intro k
    show MvPowerSeries.map (algebraMap C C) (Y.B.G.F k) = _
    rw [Algebra.algebraMap_self, MvPowerSeries.map_id]
    rfl

  have hL : MvPowerSeries.pderiv (R := C) i (Psi Y χ) =
      ∑ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    unfold Psi
    rw [pderiv_subst (og (cc_e Y))]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := expODE Y i k
    rw [hFK] at this
    show MvPowerSeries.pderiv (R := C) i (un1 (Y.ex k)) * _ = _
    rw [this]

  have h := congrArg (fun G => MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) G)) (chi_mul Y hχ)
  beta_reduce at h
  rw [Derivation.leibniz, pderiv_subst (og (cc_F Y)), pderiv_subst (og fun _ => cc_X _), pderiv_subst (og fun _ => cc_X _),
    MvPowerSeries.subst_add (hs (cc_exZero Y)), subst_sum (cc_exZero Y), smul_eq_mul, smul_eq_mul,
    subst_mul (cc_exZero Y), subst_mul (cc_exZero Y), subst_sum (cc_exZero Y), subst_sum (cc_exZero Y)] at h
  have h1 : ∀ k, MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k) *
      MvPowerSeries.subst (fun k => Y.B.G.F k) (MvPowerSeries.pderiv (R := C) k (un1 χ))) =
      MvPowerSeries.subst (exZero Y) (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (Y.B.G.F k)) *
        MvPowerSeries.subst (e Y) (MvPowerSeries.pderiv (R := C) k (un1 χ)) := by
    intro k
    rw [subst_mul (cc_exZero Y), subst_subst (cc_F Y) (cc_exZero Y)]
    congr 2
    funext k'
    exact F_exZero Y k'
  have h2 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = 0 := by
    intro k
    rw [MvPowerSeries.pderiv_X_of_ne (fun hh => by simpa using (Prod.ext_iff.1 hh).1), zero_mul,
      subst_zero' (cc_exZero Y)]
  have h3 : ∀ k, MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.pderiv (R := C) ((1 : Fin 2), i) (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd) *
      MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((1 : Fin 2), k) : PS C 2 dd))
        (MvPowerSeries.pderiv (R := C) k (un1 χ))) = if k = i then MvPowerSeries.C (dlogC χ i) else 0 := by
    intro k
    by_cases hk : k = i
    · subst hk
      rw [MvPowerSeries.pderiv_X_self, one_mul, subst_subst (fun _ => cc_X _) (cc_exZero Y), if_pos rfl]
      have : (fun s : Fin dd => MvPowerSeries.subst (exZero Y) (MvPowerSeries.X ((1 : Fin 2), s) : PS C 2 dd)) =
          fun _ => 0 := by
        funext s
        rw [subst_X (cc_exZero Y)]
        rfl
      rw [this, subst_zeroPt, constantCoeff_pderiv_uncurry]
    · rw [MvPowerSeries.pderiv_X_of_ne (fun hh => hk (Prod.ext_iff.1 hh).2), zero_mul, subst_zero' (cc_exZero Y),
        if_neg hk]
  have h4 : MvPowerSeries.subst (exZero Y)
      (MvPowerSeries.subst (fun k : Fin dd => (MvPowerSeries.X ((0 : Fin 2), k) : PS C 2 dd)) (un1 χ)) = Psi Y χ := by
    rw [subst_subst (fun _ => cc_X _) (cc_exZero Y)]
    unfold Psi
    congr 1
    funext s
    rw [subst_X (cc_exZero Y)]
    rfl
  rw [Finset.sum_congr rfl fun k _ => h1 k, Finset.sum_congr rfl fun k _ => h2 k,
    Finset.sum_congr rfl fun k _ => h3 k, Finset.sum_const_zero, mul_zero, add_zero, Finset.sum_ite_eq', h4] at h
  rw [hL, h]
  simp

theorem cc_Psi {χ : PS C 1 dd} (hχ : Y.IsChar χ) : MvPowerSeries.constantCoeff (Psi Y χ) = 1 := by
  obtain ⟨-, hχ1, -⟩ := hχ
  have hu : ∀ f : PS C 1 dd, MvPowerSeries.constantCoeff (un1 f) = MvPowerSeries.constantCoeff f := by
    intro f
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) f = _
    rw [Finsupp.mapDomain_zero]
  have he0 : ∀ k, MvPowerSeries.constantCoeff (e Y k) = 0 := fun k => (hu _).trans (Y.ex_const k)
  have hA : MvPowerSeries.HasSubst (e Y) := MvPowerSeries.hasSubst_of_constantCoeff_zero he0
  unfold Psi
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_subst hA, finsum_eq_single _ 0]
  · simp [hu, hχ1]
  · intro d hd
    obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push_neg at h
      exact hd (Finsupp.ext h)
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Finsupp.prod, map_prod,
      Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hs), smul_zero]
    rw [map_pow, he0, zero_pow hs]

theorem chi_exp {χ : PS C 1 dd} (hχ : Y.IsChar χ) : Psi Y χ = mvExp (linF (dlogC χ)) := exp_unique (dlogC χ) (Psi Y χ) (cc_Psi Y hχ) (chi_ode Y hχ)

end ChG

end Formalism.L2.FormalSeriesBounds
end
end
end

-- Source module: Formalism.LocalToGlobal.CharacterGerms.RowTieCharS

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ}
  {I0 : Type} [Fintype I0]

def SelfData.yOf {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) (χ : Fin 2 → PS C 1 dd) (x : I0) : C :=
  ∑ col, ∑ i, dlogC (χ col) i * (Y.rawSelf p).u g x (col, i)

def CharGermSelfSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ)
    (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (χ : Fin 2 → PS C 1 dd), (∀ col, Y.IsChar (χ col)) →
    ∀ (g : Fin 2) (S : ∀ g, Sys (RawChart.cart (Hc g))) (t : ∀ _ : Fin 2, I0 → MvPowerSeries I0 C),
      (∀ g, (S g).IsT (t g)) →
      upG (I := fun _ => I0) g (mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C))) ∈ IntGerm V t

namespace ChG

open VP

theorem subst_linU_linF {ι : Type} [Fintype ι] (U : ι → Fin dd → C) (y : Fin dd → C) :
    MvPowerSeries.subst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) (linF y) =
      ∑ x : ι, (∑ i, y i * U x i) • (MvPowerSeries.X x : MvPowerSeries ι C) := by
  have ha : MvPowerSeries.HasSubst (fun i => ∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) :=
    VP.hs (fun i => by

      rw [map_sum]
      refine Finset.sum_eq_zero fun c _ => ?_
      rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero])

  rw [linF, ← MvPowerSeries.coe_substAlgHom ha, map_sum]
  simp only [map_smul, MvPowerSeries.coe_substAlgHom, MvPowerSeries.subst_X ha]
  simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
  rw [Finset.sum_comm]

theorem cc_linU {ι κ : Type} [Fintype ι] (U : ι → κ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c, U c i • (MvPowerSeries.X c : MvPowerSeries ι C)) = 0 := by

  rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul, MvPowerSeries.constantCoeff_X, mul_zero]

end ChG

theorem SelfData.yOf_int {Y : FBChart C V O dd} (p : SelfData Y d I0) (g : Fin 2) {χ : Fin 2 → PS C 1 dd}
    (h : ∀ col, Y.IsChar (χ col)) (x : I0) : V.Ge 0 (p.yOf g χ x) := by
  have hsum : ∀ {ι : Type} (s : Finset ι) (f : ι → C), (∀ i ∈ s, V.Ge 0 (f i)) → V.Ge 0 (∑ i ∈ s, f i) :=
    fun s f hf => Finset.sum_induction f (fun z => V.Ge 0 z) (fun _ _ ha hb => VF.Ge.add ha hb)
      (VF.Ge.zero 0) hf
  have hgm : ∀ a r s, V.Ge 0 (p.gm a r s) := by
    intro a r s
    obtain ⟨M, hM⟩ := p.gm_lim 0
    have h1 : V.Ge 0 (p.gm a r s - p.em a (M r s)) := by simpa using hM a r s
    have h2 := VF.Ge.add h1 (p.em_int a (M r s))
    simpa using h2
  unfold SelfData.yOf
  refine hsum _ _ fun col _ => hsum _ _ fun i _ => ?_
  refine VF.Ge.mul_int ((h col).1 _) ?_
  exact VF.Ge.mul_int (hgm _ _ _) (p.e_int _ _)

open ChG VP in
theorem charGermSelf_holds : CharGermSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p Hc χ hχ g S t ht
  obtain ⟨P, hP0, hPI, -, hPt⟩ := GeneralGermZero.sysK_P (Y.rawSelf p) (SelfConjugateGermZero.lawS Y) (SelfConjugateGermZero.lawS_const Y) (SelfConjugateGermZero.lawS_int Y)
    (SelfConjugateGermZero.lgS_add Y p) (SelfConjugateGermZero.lgS_lin Y p) (SelfConjugateGermZero.exS_lg Y p) (Hc g) (S g)
  have ht0 : ∀ g c, MvPowerSeries.constantCoeff (t g c) = 0 := fun g c => (ht g).1 c
  set U : I0 → Fin 2 × Fin dd → C := fun c' i => (Y.rawSelf p).u g c' i with hU
  set γ0 : MvPowerSeries I0 C := ∏ col : Fin 2, MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col)) with hγ0
  have hI : IntS V γ0 := IntS_prod _ fun col _ =>
    IntS.subst (fun i => hP0 (col, i)) (fun i => hPI (col, i)) (integralSeries_uncurry_one (hχ col).1)
  have hcol : ∀ col : Fin 2, MvPowerSeries.subst (t g) (MvPowerSeries.subst (fun i => P (col, i)) (un1 (χ col))) =
      mvExp (∑ x : I0, (∑ i, dlogC (χ col) i * U x (col, i)) • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    intro col
    rw [subst_subst (fun i => hP0 (col, i)) (ht0 g)]
    have h1 : (fun i => MvPowerSeries.subst (t g) (P (col, i))) = fun i =>
        MvPowerSeries.subst (fun k : Fin dd => ∑ c', U c' (col, k) • (MvPowerSeries.X c' : MvPowerSeries I0 C)) (e Y i) := by
      funext i
      rw [hPt (t g) (ht g) (col, i)]
      show MvPowerSeries.subst (fun k : Fin 2 × Fin dd => ∑ c', U c' k • (MvPowerSeries.X c' : MvPowerSeries I0 C))
        (MvPowerSeries.subst (fun x : Fin dd => (MvPowerSeries.X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C))
          (un1 (Y.ex i))) = _
      rw [subst_subst (fun _ => cc_X _) (cc_linU U)]
      congr 1
      funext k
      rw [subst_X (cc_linU U)]
    rw [h1, ← subst_subst (cc_e Y) (fun k => cc_linU U (col, k))]
    show MvPowerSeries.subst _ (Psi Y (χ col)) = _
    rw [chi_exp Y (hχ col), subst_exp (fun k => cc_linU U (col, k)) (constantCoeff_linF _),
      subst_linU_linF (fun c' k => U c' (col, k))]
  have key : MvPowerSeries.subst (t g) γ0 =
      mvExp (∑ x : I0, p.yOf g χ x • (MvPowerSeries.X x : MvPowerSeries I0 C)) := by
    rw [hγ0, subst_prod (ht0 g), Finset.prod_congr rfl fun col _ => hcol col,
      ← Formalism.UnitaryBoundIntegral.ubint_mvExp_sum Finset.univ _ (fun col _ => cc_linU (fun x (_ : Unit) => ∑ i, dlogC (χ col) i * U x (col, i)) ()),
      Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_smul]
    rfl
  refine ⟨upG (I := fun _ => I0) g γ0, ?_, ?_⟩
  · exact IntS.subst (fun _ => cc_X _) (fun _ => IntS_X _) hI
  · rw [AbstractGermZero.upG_subst (I := fun _ => I0) t ht0 g, key]

section Chart

open Formalism.L2.Pj NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)]

end Chart

end Formalism.L2.FormalSeriesBounds
end
end
end
