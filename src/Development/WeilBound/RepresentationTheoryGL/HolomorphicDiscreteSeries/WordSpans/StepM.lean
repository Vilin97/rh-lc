module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpan
public import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
public import Development.WeilBound.CoreStatements.BranchingTraces.ExistsIntertwiner
import Development.WeilBound.CoreStatements.BranchingTraces.FormTSingle
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.ContinuousUmInv
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.EmbRow
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.ExistsDs
public import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.ContDiffEmb
public import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.OneLeDiff
import Development.WeilBound.CoreStatements.BranchingTraces.BranchingComatrices.RootOfNe
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.QminorInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.HaveILetI
public import Development.WeilBound.CoreStatements.BranchingTraces.ContinuousEmb

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.NonVanishing

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpanNonVanishing

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com

theorem nonvan (hKey : KeyId) {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (hP0 : P ≠ 0) (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1))
    (hj : j ∈ X.S) (hwall : ∀ s, mu j - 1 / 2 ≠ lam s) : ∃ η ∈ S, X.p j (phi E e P η) ≠ 0 := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  have hιinj : Function.Injective ι := fun a b h => Sum.inl_injective (e.injective h)
  have hιz : ∀ a, ι a ≠ z := by
    intro a h
    have := e.injective h
    simp at this
  have hPS : ∀ v : S, P v ∈ S' := fun v =>
    (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPS v⟩
      map_add' := by
        intro x y
        ext
        simp
      map_smul' := by
        intro c x
        ext
        simp }
  have hfv : ∀ v : S, ((f v : S') : H') = P v := fun v => rfl
  have hf : ∀ (a b : Fin (N + 1)) (x : S), f (E (ι a) (ι b) x) = E' a b (f x) := by
    intro a b x
    ext
    rw [hfv, hS.act, hS'.act, hfv, ← blk_single e a b]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX x).differentiableAt) (single a b 1)
  set mπ : Fin (N + 2) → ℂ := fun s => (lam s : ℂ) - (((N + 2 : ℕ) : ℂ) - 1) / 2 with hmπ
  set mσ : Fin (N + 1) → ℂ := fun s => (mu s : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hmσ
  have hcapπ : ∀ (u : ℂ) (v : S), qdet E u v = (∏ s, (u + mπ s)) • v := cap_of hG.hc hπ hS
  have hcapσ : ∀ (u : ℂ) (v : S'), qdet E' u v = (∏ s, (u + mσ s)) • v := cap_of hG.hc' hσ hS'
  have hw0 : ∀ y : S', qdet E' (-mσ j) y = 0 := by
    intro y
    rw [hcapσ, Finset.prod_eq_zero (Finset.mem_univ j) (by ring), zero_smul]
  set cG : ℂ := ∏ s, (-mσ j + 1 + mπ s) with hcGdef
  have hcG : cG ≠ 0 := by
    rw [hcGdef, Finset.prod_ne_zero_iff]
    intro s _ h
    apply hwall s
    have h' : -((mu j : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2) + 1 + ((lam s : ℂ) - (((N + 2 : ℕ) : ℂ) - 1) / 2) = 0 := h
    push_cast at h'
    have h2 : ((mu j - 1 / 2 : ℝ) : ℂ) = (lam s : ℂ) := by
      push_cast
      linear_combination -h'
    exact_mod_cast h2
  have hK : ∀ v : S, cG • f v = -∑ c : Fin (N + 1),
      (Th E' (-mσ j)) (fun l => f ((E (ι l) z) ((E z (ι c)) v))) c :=
    fun v => hKey S S' N E E' ι z f hS.gl hιinj hιz hf (-mσ j) cG (fun x => hcapπ _ x) hw0 v
  by_contra hno
  push_neg at hno
  let lift : (Fin (N + 1) → H') → Fin (N + 1) → S' := fun y l =>
    if h : y l ∈ S' then ⟨y l, h⟩ else 0
  have hlift : ∀ y ∈ SmT ε' σ, ∀ l, ((lift y l : S') : H') = y l := by
    intro y hy l
    simp [lift, (hS'.mem _).2 (hy l)]
  have hT0 : ∀ u : S, (Th E' (-mσ j)) (fun l => f ((E (ι l) z) u)) = 0 := by
    intro u
    set x : Fin (N + 1) → H' := phi E e P (u : H) with hxdef
    have hxl : ∀ l, x l = P ((E (ι l) z) u) := by
      intro l
      simp [hxdef, phi, ap, u.2, hι, hz]
    have hx : x ∈ SmT ε' σ := by
      intro l
      rw [hxl]
      exact (hS'.mem _).1 (hPS _)
    have hsum : ∑ t ∈ X.S, lift (X.p t x) = fun l => f ((E (ι l) z) u) := by
      funext l
      apply Subtype.ext
      rw [Finset.sum_apply, Submodule.coe_sum]
      have : ∀ t ∈ X.S, ((lift (X.p t x) l : S') : H') = X.p t x l :=
        fun t ht => hlift _ (X.p_sm t ht x hx) l
      rw [Finset.sum_congr rfl this, ← Finset.sum_apply, X.sum x hx, hxl, hfv]
    have heig : ∀ t ∈ X.S, (EE E') (lift (X.p t x)) = X.κ t • lift (X.p t x) := by
      intro t ht
      have hsm := X.p_sm t ht x hx
      funext c
      apply Subtype.ext
      have hcas := congrFun (X.cas t ht x hx) c
      simp only [casT, Pi.smul_apply] at hcas
      simp only [EE, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.coe_comp,
        Function.comp_apply, LinearMap.coe_proj, Function.eval, Pi.smul_apply, Submodule.coe_smul,
        Submodule.coe_sum]
      rw [hlift _ hsm c, ← hcas]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [hS'.act, hlift _ hsm l]
    have hκj : X.κ j = (N : ℂ) + mσ j := by
      rw [hκ j, hmσ]
      push_cast
      ring
    have hproj := th_proj hS'.gl hcapσ X.S (fun t => lift (X.p t x)) X.κ X.κ_inj heig hj j hκj
    rw [hsum] at hproj
    rw [hproj]
    have hpj : lift (X.p j x) = 0 := by
      rw [hno _ u.2]
      funext l
      simp [lift]
    rw [hpj, smul_zero]
  have hPv : ∀ v : S, P v = 0 := by
    intro v
    have h1 := hK v
    simp only [hT0, Pi.zero_apply, Finset.sum_const_zero, neg_zero] at h1
    have h2 : f v = 0 := (smul_eq_zero.1 h1).resolve_left hcG
    have h3 := congrArg (fun y : S' => (y : H')) h2
    simpa [hfv] using h3
  have hgap : Formalism.QuantumDeterminants.GapAtLeast ε lam (100 * ((N + 2 : ℕ) : ℝ) ^ 3) := by
    intro a b hab
    refine le_trans ?_ (hG.gap a b hab)
    push_cast
    have : (0 : ℝ) ≤ ((N : ℝ) + 2) ^ 3 := by positivity
    nlinarith
  have hdense : Dense (S : Set H) :=
    PositivityTheory.RgHe.SM.dense_sm (by omega) hG.hc hπ hgap hS
  apply hP0
  have heq := Continuous.ext_on hdense P.continuous (continuous_const (y := (0 : H')))
    (fun x hx => hPv ⟨x, hx⟩)
  ext x
  simpa using congrFun heq x

end PositivityTheory.RgHe.SM.WordSpanNonVanishing
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.WordSpaces

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM.WordSpaces

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC PositivityTheory.UnitaryDecomposition.Com PositivityTheory.RgHe.SM

section WS

variable {V : Type} [AddCommGroup V] [Module ℂ V] {m : ℕ} (E : Fin m → Fin m → Module.End ℂ V)

theorem one_mem_ws (L : ℕ) : (1 : Module.End ℂ V) ∈ wordSpan E L :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

theorem gen_mem_ws (a b : Fin m) : E a b ∈ wordSpan E 1 :=
  Submodule.subset_span ⟨[(a, b)], by simp, by simp⟩

theorem ws_mul {L L' : ℕ} {T T' : Module.End ℂ V} (hT : T ∈ wordSpan E L) (hT' : T' ∈ wordSpan E L') :
    T * T' ∈ wordSpan E (L + L') := by
  have key : wordSpan E L * wordSpan E L' ≤ wordSpan E (L + L') := by
    unfold wordSpan
    rw [Submodule.span_mul_span]
    refine Submodule.span_mono ?_
    rintro _ ⟨A, ⟨w, hw, rfl⟩, B, ⟨w', hw', rfl⟩, rfl⟩
    exact ⟨w ++ w', by simp only [List.length_append]; omega, by simp [List.map_append, List.prod_append]⟩
  exact key (Submodule.mul_mem_mul hT hT')

variable {k : ℕ} (F : Fin k → Fin k → Module.End ℂ V)

theorem tm_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) (u : ℂ) (a b : Fin k) : Tm F u a b ∈ wordSpan E 1 := by
  unfold Tm
  refine Submodule.add_mem _ ?_ (hF a b)
  split_ifs
  · rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (one_mem_ws E 1)
  · exact Submodule.zero_mem _

theorem prod_mem_ws (l : List (Module.End ℂ V)) (h : ∀ x ∈ l, x ∈ wordSpan E 1) : l.prod ∈ wordSpan E l.length := by
  induction l with
  | nil => simpa using one_mem_ws E 0
  | cons x l ih =>
    rw [List.prod_cons, List.length_cons, add_comm]
    exact ws_mul E (h x (by simp)) (ih fun y hy => h y (by simp [hy]))

theorem qminor_mem (hF : ∀ a b, F a b ∈ wordSpan E 1) {t : ℕ} (a b : Fin t → Fin k) (u : ℂ) :
    qminor F a b u ∈ wordSpan E t := by
  unfold qminor
  refine Submodule.sum_mem _ fun σ _ => ?_
  have h := prod_mem_ws E (List.ofFn fun i : Fin t => Tm F (u - (i : ℂ)) (a (σ i)) (b i)) (by
    intro x hx
    rw [List.mem_ofFn] at hx
    obtain ⟨i, rfl⟩ := hx
    exact tm_mem E F hF _ _ _)
  rw [List.length_ofFn] at h
  rw [← zsmul_eq_mul]
  exact zsmul_mem h _

end WS

theorem pj_words {N : ℕ} {ε : Fin (N + 2) → Bool} {ε' : Fin (N + 1) → Bool} {e : Fin (N + 1) ⊕ Unit ≃ Fin (N + 2)}
    {lam : Fin (N + 2) → ℝ} {mu : Fin (N + 1) → ℝ} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H'] {π : Matrix (Fin (N + 2)) (Fin (N + 2)) ℂ → (H →L[ℂ] H)}
    {σ : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → (H' →L[ℂ] H')} {S : Submodule ℂ H} {E : Fin (N + 2) → Fin (N + 2) → Module.End ℂ S}
    {S' : Submodule ℂ H'} {E' : Fin (N + 1) → Fin (N + 1) → Module.End ℂ S'} {P : H →L[ℂ] H'} (hG : Gp ε lam ε' mu e)
    (hπ : IsDS ε lam π) (hσ : IsDS ε' mu σ) (hS : IsSmMod ε π S E) (hS' : IsSmMod ε' σ S' E') (hP : Intertw ε' e π σ P)
    (X : Dec ε' mu σ) (hκ : ∀ s, X.κ s = (mu s : ℂ) + (((N + 1 : ℕ) : ℂ) - 1) / 2) (j : Fin (N + 1)) (hj : j ∈ X.S) :
    ∃ R : Fin (N + 1) → Module.End ℂ S, (∀ l, R l ∈ wordSpan E (N + 1)) ∧
      ∀ ζ ∈ S, ∀ l, X.p j (phi E e P ζ) l = P (ap (R l) ζ) := by
  classical
  set ι : Fin (N + 1) → Fin (N + 2) := fun a => e (Sum.inl a) with hι
  set z : Fin (N + 2) := zi e with hz
  set m : Fin (N + 1) → ℂ := fun i => (mu i : ℂ) - (((N + 1 : ℕ) : ℂ) - 1) / 2 with hm
  have hq : ∀ u v, qdet E' u v = (∏ i, (u + m i)) • v := cap_of hG.hc' hσ hS'
  set w : ℂ := -m j with hw
  have hPs : ∀ v : S, P v ∈ S' := fun v => (hS'.mem _).2 (smooth_map hG.fits hP ((hS.mem _).1 v.2))
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun v => ⟨P v, hPs v⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  have hf : ∀ a b (v : S), f (E (ι a) (ι b) v) = E' a b (f v) := fun a b v => Subtype.ext (by
    show P (E (ι a) (ι b) v : H) = (E' a b (f v) : H')
    rw [hS.act, hS'.act, ← blk_single (e := e)]
    exact dsigC_map hG.fits hP (fun X hX => (hS.real X hX v).differentiableAt) _)
  let co : (Fin (N + 1) → S') → Fin (N + 1) → H' := fun x l => x l
  have hco : ∀ x, co x ∈ SmT ε' σ := fun x l => (hS'.mem _).1 (x l).2
  let Y : (Fin (N + 1) → S') → X.S → Fin (N + 1) → S' := fun x t c =>
    ⟨X.p t (co x) c, (hS'.mem _).2 (X.p_sm t t.2 _ (hco x) c)⟩
  have hYe : ∀ x t, EE E' (Y x t) = X.κ t • Y x t := fun x t => funext fun c => Subtype.ext (by
    have := congrFun (X.cas t t.2 _ (hco x)) c
    rw [EE_apply, Submodule.coe_sum]
    simp only [hS'.act]
    exact this)
  have hYs : ∀ x, ∑ t, Y x t = x := fun x => funext fun c => Subtype.ext (by
    have := congrFun (X.sum _ (hco x)) c
    rw [Finset.sum_apply] at this
    rw [Finset.sum_apply, Submodule.coe_sum]
    exact (Finset.sum_coe_sort X.S fun t => X.p t (co x) c).trans this)
  set d : ℂ := ∏ i ∈ univ.erase j, (-m j + m i) with hd
  have hd0 : d ≠ 0 := by
    rw [hd, Finset.prod_ne_zero_iff]
    intro i hi h0
    have hne : i ≠ j := Finset.ne_of_mem_erase hi
    have : mu i = mu j := by
      have h1 : (mu i : ℂ) = mu j := by simp only [hm] at h0; linear_combination h0
      exact_mod_cast h1
    exact hne (hG.hc'.1.injective this)
  have hth : ∀ x, Th E' w x = d • Y x ⟨j, hj⟩ := fun x => by
    have h := th_proj hS'.gl hq univ (Y x) (fun t : X.S => X.κ t)
      (fun a _ b _ h => Subtype.ext (X.κ_inj a.2 b.2 h)) (fun t _ => hYe x t) (mem_univ (⟨j, hj⟩ : X.S)) j
      (by rw [hκ]; simp only [hm]; push_cast; ring)
    rwa [hYs] at h
  let T : Fin (N + 1) → Module.End ℂ S := fun l =>
    ∑ a : Fin (N + 1), ((-1 : ℂ) ^ ((a : ℕ) + (l : ℕ))) •
      (qminor (fun a b => E (ι a) (ι b)) a.succAbove l.succAbove w * E (ι a) z)
  refine ⟨fun l => d⁻¹ • T l, fun l => ?_, fun ζ hζ l => ?_⟩
  · refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_)
    exact ws_mul E (qminor_mem E _ (fun a b => gen_mem_ws E _ _) _ _ _) (gen_mem_ws E _ _)
  · set ζ' : S := ⟨ζ, hζ⟩
    let X0 : Fin (N + 1) → S := fun a => E (ι a) z ζ'
    let x : Fin (N + 1) → S' := fun c => f (X0 c)
    have hco' : co x = phi E e P ζ := funext fun c => by
      simp only [co, x, X0, phi, ap, dif_pos hζ]
      rfl
    have hT : T l ζ' = Th (fun a b => E (ι a) (ι b)) w X0 l := by
      rw [Th_apply]
      simp only [T, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
      rfl
    have h1 : P (ap (d⁻¹ • T l) ζ) = d⁻¹ • (f (Th (fun a b => E (ι a) (ι b)) w X0 l) : H') := by
      simp only [ap, dif_pos hζ, LinearMap.smul_apply, Submodule.coe_smul, map_smul]
      rw [hT]
      rfl
    have h2 := (thMap S S' N (fun a b => E (ι a) (ι b)) E' f hf w X0 l).1
    rw [h1, h2, show (fun l => f (X0 l)) = x from rfl, hth x, ← hco']
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_smul, inv_mul_cancel₀ hd0, one_smul]
    rfl

end PositivityTheory.RgHe.SM.WordSpaces
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.ModelWalkOfInputs

section

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.SM

open Formalism.REAL Formalism.MainNotions.S PositivityTheory.UnitaryDecomposition Formalism.FourierDecayAlt.P.CapelliAbstractCharacter CompanionTheory.D.DSIC

theorem gap_mono {m : ℕ} {ε : Fin m → Bool} {lam : Fin m → ℝ} {h h' : ℝ} (hg : Formalism.QuantumDeterminants.GapAtLeast ε lam h) (hh : h' ≤ h) :
    Formalism.QuantumDeterminants.GapAtLeast ε lam h' := fun a b hab => hh.trans (hg a b hab)


theorem stepM_of (hKey : KeyId) (hZ : Zero) (hPhi : PhiEq) (hIrr : Irr) :
    Models → OfInt → Seed → DecEx2 → StepM := by
  intro hMod hOf _ hDec n ε lam ε' mu e hG j hG' hwall hOcc
  refine (hMod n ε lam ε' (mu - Pi.single j 1) e hG').1 ?_
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by have := hG.two; omega⟩
  have hN1 : 1 ≤ N + 1 := by omega
  have hc1 : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have gG : Formalism.QuantumDeterminants.GapAtLeast ε lam (200 * ((N + 2 : ℕ) : ℝ) ^ 3) := by
    have h := hG.gap
    refine gap_mono h (le_of_eq ?_)
    push_cast; ring
  have gH : Formalism.QuantumDeterminants.GapAtLeast ε' mu (200 * ((N + 1 : ℕ) : ℝ) ^ 3) :=
    gap_mono hG.gap' (by have : ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by linarith
                         have := pow_le_pow_left₀ hc1 this 3; linarith)
  obtain ⟨H, i1, i2, π, hπ⟩ := exists_ds ε lam (by omega) hG.hc gG
  obtain ⟨H', i3, i4, σ, hσ⟩ := exists_ds ε' mu hN1 hG.hc' gH
  haveI : CompleteSpace H := hπ.1
  haveI : CompleteSpace H' := hσ.1
  obtain ⟨j0, hj0, hj0m⟩ := hOcc H H' π σ hπ hσ
  obtain ⟨P, hP, hP0⟩ := exists_P hG.fits hπ hσ hj0 hj0m
  obtain ⟨S, E, hS⟩ := hSmMod (N + 2) ε H π hπ.2.2.1
  obtain ⟨S', E', hS'⟩ := hSmMod (N + 1) ε' H' σ hσ.2.2.1
  obtain ⟨X, hXS, hXκ⟩ := hDec (N + 1) ε' mu H' σ (signs hG).1 (signs hG).2 hG.hc' hσ gH
  have hj : j ∈ X.S := (hXS j).2 hG'.hc'
  have hσ' := (X.ds j hj).2
  obtain ⟨η₀, hη₀, hne⟩ := WordSpanNonVanishing.nonvan hKey hG hπ hσ hS hS' hP hP0 X hXκ j hj hwall
  obtain ⟨R, hR, hRe⟩ := WordSpaces.pj_words hG hπ hσ hS hS' hP X hXκ j hj
  have hUπ := hπ.2.2.1
  have hUσ := hσ.2.2.1
  have hden : Dense (S : Set H) :=
    dense_sm (by omega) hG.hc hπ (gap_mono gG (by have : (0 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) ^ 3 := by positivity
                                                  linarith)) hS

  have hφ₀ := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).1
  have hx₀ := X.p_sm j hj _ hφ₀
  obtain ⟨l, hl⟩ : ∃ l, X.p j (phi E e P η₀) l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hy := smT_single (hx₀ l) l
  have hform := X.form j hj _ hφ₀ _ hy
  rw [formT_single] at hform
  have hprod : X.c j * ⟪X.pr j (Pi.single l (X.p j (phi E e P η₀) l)), X.pr j (phi E e P η₀)⟫_ℂ ≠ 0 := by
    rw [← hform]
    refine mul_ne_zero (by split_ifs <;> norm_num) ?_
    rw [inner_self_ne_zero]; exact hl
  have hcj : X.c j ≠ 0 := left_ne_zero_of_mul hprod
  have hpr2 := right_ne_zero_of_mul hprod
  have hpry : X.pr j (Pi.single l (X.p j (phi E e P η₀) l)) ≠ 0 := fun h0 => hpr2 (by rw [h0, inner_zero_left])
  have hprφ : X.pr j (phi E e P η₀) ≠ 0 := fun h0 => hpr2 (by rw [h0, inner_zero_right])
  obtain ⟨w', hw', hw'1⟩ := exists_low hσ'
  have hw'0 : w' ≠ 0 := fun h0 => by rw [h0, norm_zero] at hw'1; exact zero_ne_one hw'1
  obtain ⟨h₁, hh₁⟩ := hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hprφ hw'0
  obtain ⟨h₂, hh₂⟩ := hIrr (N + 1) ε' _ (X.πs j) hσ'.2.2.1 hσ'.2.2.2.1 _ w' hpry hw'0
  set y := (Pi.single l (X.p j (phi E e P η₀) l) : Fin (N + 1) → H') with hyd
  have hmem : ∀ h : UJ ε', emb e (um h) ∈ UJset ε := fun h => Formalism.MainNotions.BridgeCSchur.umat_mem (embU hG.fits h)
  set η₁ := π (emb e (um h₁)) η₀ with hη₁d
  have hη₁ : η₁ ∈ S := hS.stab _ (hmem h₁) η₀ hη₀
  have hφ₁e := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₀ hη₀).2 h₁
  have hφ₁ := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).1
  have hprφ₁ : X.pr j (phi E e P η₁) = X.πs j (um h₁) (X.pr j (phi E e P η₀)) := by
    rw [hφ₁e]; exact X.pr_act j hj h₁ _ hφ₀
  set y₂ := actT σ (um h₂) y with hy₂d
  have hy₂ : y₂ ∈ SmT ε' σ := smT_act hUσ h₂ hy
  have hpry₂ : X.pr j y₂ = X.πs j (um h₂) (X.pr j y) := X.pr_act j hj h₂ _ hy
  have hA : ⟪X.pr j y₂, w'⟫_ℂ ≠ 0 := by
    rw [hpry₂, ← inner_conj_symm]; exact (map_ne_zero _).2 hh₂
  have hB : ⟪w', X.pr j (phi E e P η₁)⟫_ℂ ≠ 0 := by rw [hprφ₁]; exact hh₁
  obtain ⟨κ', hκ', hsch⟩ := schur_haar hσ' (muG ε')
  obtain ⟨hcont, C, hCb⟩ := decay_low hN1 hG'.hc' hσ' hG'.gap' hw' hw'1
  by_contra hnot
  have hall : ∀ a b : H, ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * ⟪b, π (emb e (um h)) a⟫_ℂ ∂(muG ε') = 0 := by
    intro a b
    by_contra hab
    obtain ⟨j1, hj1, hj1m⟩ := hOf (N + 1) ε lam ε' (mu - Pi.single j 1) e hG' H (X.Hs j) π (X.πs j) (muG ε') inferInstance
      hπ hσ' w' hw' hw'1 a b hab
    exact hnot ⟨H, X.Hs j, inferInstance, inferInstance, inferInstance, inferInstance, π, X.πs j, hπ, hσ', j1, hj1, hj1m⟩
  have hZl := fun l' => hZ (N + 1) ε ε' e H π S E hG.fits hN1 hS hUπ hden (muG ε') inferInstance
    (fun h : UJ ε' => conj ⟪w', X.πs j (um h) w'⟫_ℂ) (N + 1) C hcont hCb hall (R l') (hR l') ⟨η₁, hη₁⟩
    (ContinuousLinearMap.adjoint P (y₂ l'))
  have hpt : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) =
      ∑ l', (if ε' l' then 1 else -1) * (conj ⟪w', X.πs j (um h) w'⟫_ℂ *
        ⟪ContinuousLinearMap.adjoint P (y₂ l'), ap (R l') (π (emb e (um h)) η₁)⟫_ℂ) := by
    intro h
    have e2 : ∀ l', X.p j (phi E e P (π (emb e (um h)) η₁)) l' = P (ap (R l') (π (emb e (um h)) η₁)) :=
      hRe _ (hS.stab _ (hmem h) η₁ hη₁)
    simp only [formT, e2, ← ContinuousLinearMap.adjoint_inner_left, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l' _ => by ring
  have hpt2 : ∀ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) =
      X.c j * (⟪X.pr j y₂, X.πs j (um h) (X.pr j (phi E e P η₁))⟫_ℂ * conj ⟪w', X.πs j (um h) w'⟫_ℂ) := by
    intro h
    have e1 := (hPhi (N + 1) ε ε' e H H' π σ S E P hG.fits hS hUπ hP η₁ hη₁).2 h
    rw [e1, X.form j hj _ (smT_act hUσ h hφ₁) _ hy₂, X.pr_act j hj h _ hφ₁]
    ring
  have hI0 : ∫ h : UJ ε', conj ⟪w', X.πs j (um h) w'⟫_ℂ * formT ε' y₂ (X.p j (phi E e P (π (emb e (um h)) η₁))) ∂(muG ε') = 0 := by
    rw [integral_congr_ae (.of_forall hpt), integral_finsetSum _ fun l' _ => (hZl l').1.const_mul _]
    exact Finset.sum_eq_zero fun l' _ => by rw [integral_const_mul, (hZl l').2, mul_zero]
  rw [integral_congr_ae (.of_forall hpt2), integral_const_mul, (hsch _ _ _ _).2] at hI0
  have hκ0 : (κ' : ℂ) ≠ 0 := by exact_mod_cast hκ'.ne'
  exact mul_ne_zero hcj (mul_ne_zero hκ0 (mul_ne_zero hB hA)) hI0

end PositivityTheory.RgHe.SM

namespace PositivityTheory.RgHe.SM

theorem model_walk_of_inputs : Models → OfInt → Seed → DecEx2 → StepM := stepM_of keyId zero_proof phiEq irr

end PositivityTheory.RgHe.SM
end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WordSpans.StepM

section

@[expose] public section

namespace PositivityTheory.RgHe.SM

theorem stepM : PositivityTheory.RgHe.Models → PositivityTheory.RgHe.OfInt → PositivityTheory.RgHe.Seed → PositivityTheory.RgHe.DecEx2 → PositivityTheory.RgHe.StepM := model_walk_of_inputs

end PositivityTheory.RgHe.SM
end
end
