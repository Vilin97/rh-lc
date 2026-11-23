module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.BackStable
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeDuality.DualModuleFacts
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.HeckeUnits.Unitarity
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.ScalarCharacters.ScalCharOfSimple
public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.SimpleBackwardTransfer.FwdSimpleOfb
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CayleyHamiltonStatementStatement
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ReduceModChar
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeNonVanishingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InfinitesimalCharacterStatementStatement
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantEqualityStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.QuantumDeterminantTensorStatement

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.TensorReflections.PiIsoTensVd

section

@[expose] public section

noncomputable section

namespace CompanionTheory.RgExh.Hk

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli

variable {n : ℕ}

theorem iso_symm' {X X' : GMod n} (h : Iso X X') : Iso X' X := by
  obtain ⟨e, he⟩ := h
  refine ⟨e.symm, fun a b x => ?_⟩
  apply e.injective
  rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem iso_trans' {X X' X'' : GMod n} (h : Iso X X') (h' : Iso X' X'') : Iso X X'' := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  exact ⟨e.trans e', fun a b x => by simp [he, he']⟩

theorem map_maxGen {M M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (φ : M ≃ₗ[ℂ] M') (T : Module.End ℂ M) (T' : Module.End ℂ M') (hφ : ∀ x, φ (T x) = T' (φ x)) (μ : ℂ) :
    (T.maxGenEigenspace μ).map (φ : M →ₗ[ℂ] M') = T'.maxGenEigenspace μ := by
  have key : ∀ (k : ℕ) (x : M), φ (((T - μ • (1 : Module.End ℂ M)) ^ k) x) =
      ((T' - μ • (1 : Module.End ℂ M')) ^ k) (φ x) := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]
      congr 1
      simp [hφ]
  ext y
  rw [Submodule.mem_map_equiv, Module.End.mem_maxGenEigenspace, Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := key k (φ.symm y)
    rw [hk, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply φ.injective
    rw [key, LinearEquiv.apply_symm_apply, hk, map_zero]

theorem iso_sub' {X X' : GMod n} (φ : X.V ≃ₗ[ℂ] X'.V) (hφ : ∀ a b x, φ (X.E a b x) = X'.E a b (φ x))
    (S : Submodule ℂ X.V) (S' : Submodule ℂ X'.V) (hS : S.map (φ : X.V →ₗ[ℂ] X'.V) = S')
    (h : ∀ a b, ∀ x ∈ S, X.E a b x ∈ S) (h' : ∀ a b, ∀ x ∈ S', X'.E a b x ∈ S') :
    Iso (X.sub S h) (X'.sub S' h') :=
  ⟨φ.ofSubmodules S S' hS, fun a b x => Subtype.ext (hφ a b x.1)⟩

def piIso {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) : (Fin n → X.V) ≃ₗ[ℂ] (Fin n → X'.V) :=
  LinearEquiv.piCongrRight fun _ : Fin n => e

theorem piIso_tensVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (a b : Fin n) (f : Fin n → X.V) : piIso e (tensVd X.E a b f) = tensVd X'.E a b (piIso e f) := by
  funext d
  by_cases hd : d = b
  · subst hd
    simp [piIso, tensVd, he]
  · simp [piIso, tensVd, he, hd]

theorem piIso_eeVd {X X' : GMod n} (e : X.V ≃ₗ[ℂ] X'.V) (he : ∀ a b x, e (X.E a b x) = X'.E a b (e x))
    (f : Fin n → X.V) : piIso e (eeVd X.E f) = eeVd X'.E (piIso e f) := by
  funext a

  simp [piIso, eeVd, he, map_sum]

theorem iso_back' {Y Y' : GMod n} (hY : Iso Y Y') (z : ℂ)
    (h : ∀ a b, ∀ x ∈ backSub Y z, (tensD Y).E a b x ∈ backSub Y z)
    (h' : ∀ a b, ∀ x ∈ backSub Y' z, (tensD Y').E a b x ∈ backSub Y' z) :
    Iso (back Y z h) (back Y' z h') := by
  obtain ⟨e, he⟩ := hY
  exact iso_sub' (X := tensD Y) (X' := tensD Y') (piIso e) (fun a b f => piIso_tensVd e he a b f) _ _
    (map_maxGen (piIso e) (omD Y) (omD Y') (fun f => piIso_eeVd e he f) _) h h'

theorem reflect_of' : QdetTens → OmScal → BackStable → DualFacts → Unit → Reflect := by
  intro _ hOm hB _ hU n X X' χ s hX hX' hfree hsimp hiso
  have h1 := hU n X χ s hB hX hfree hsimp (hOm n X χ s hX hsimp)
  have h2 := hU n X' χ s hB hX' hfree hsimp (hOm n X' χ s hX' hsimp)
  exact iso_trans' (iso_symm' h1) (iso_trans' (iso_back' hiso _ _ _) h2)

end CompanionTheory.RgExh.Hk
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStable

section

@[expose] public section

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgHeckeBack

open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk

variable {n : ℕ}

theorem tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by
  by_cases h : i = b <;> simp [tensVd, h]

theorem eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by
  simp [eeVd]

theorem commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by
  refine LinearMap.ext fun f => funext fun a => ?_

  simp only [Module.End.mul_apply, tensVd_apply, eeVd_apply, map_neg, map_sum, map_sub]
  simp only [comm_apply X c d a _ _, sum_sub_distrib, sum_add_distrib, apply_ite (X.E a _), map_zero]
  by_cases h : a = d
  · subst h
    simp
    abel
  · simp [h, Ne.symm h]

theorem backStable : BackStable := fun _ X z a b _ hx =>
  Module.End.mapsTo_maxGenEigenspace_of_comm (commute_tensVd_eeVd X a b).symm (-z - cn _) hx

end GlobalTheory.CompanionTheory.RgHeckeBack
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeBackwardStableStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.HeckeBackwardStable : CompanionTheory.RgExh.Hk.BackStable := by
  first | exact @GlobalTheory.CompanionTheory.RgHeckeBack.backStable | exact GlobalTheory.CompanionTheory.RgHeckeBack.backStable | (intros; apply GlobalTheory.CompanionTheory.RgHeckeBack.backStable <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaScalar

section

@[expose] public section

noncomputable section

open Finset Polynomial

namespace GlobalTheory.CompanionTheory.RgExhHecke.OmScalP

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

section Poly

variable {A : Type*} [Ring A] [Algebra ℂ A]

def evAt (u : ℂ) : A[X] →+* A :=
  eval₂RingHom' (RingHom.id A) (algebraMap ℂ A u) fun a => (Algebra.commutes u a).symm

theorem evAt_apply (u : ℂ) (p : A[X]) : evAt u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := rfl

def tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v : ℂ) (a b : Fin n) : A[X] :=
  (if a = b then X - C (algebraMap ℂ A v) else 0) + C (E a b)

theorem evAt_tmPoly {n : ℕ} (E : Fin n → Fin n → A) (v u : ℂ) (a b : Fin n) :
    evAt u (tmPoly E v a b) = Tm E (u - v) a b := by
  unfold tmPoly Tm
  by_cases h : a = b <;> simp [h, evAt_apply, map_sub]

def qdetPoly {n : ℕ} (E : Fin n → Fin n → A) : A[X] :=
  ∑ σ : Equiv.Perm (Fin n), (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : A[X]) *
    (List.ofFn fun k : Fin n => tmPoly E ((k : ℕ) : ℂ) (σ k) k).prod

theorem evAt_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evAt u (qdetPoly E) = qdet E u := by
  unfold qdet qminor qdetPoly

  rw [map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  simp [Function.comp_def, evAt_tmPoly]

end Poly

theorem cont {M : Type*} [AddCommGroup M] [Module ℂ M] (p : (Module.End ℂ M)[X]) (q : ℂ[X]) (h : M) (b : ℂ)
    (H : ∀ u, u ≠ b → evAt u p h = q.eval u • h) : evAt b p h = q.eval b • h := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  set r : ℂ[X] := ∑ k ∈ p.support, monomial k (φ (p.coeff k h)) - q * C (φ h) with hr
  have hev : ∀ u, r.eval u = φ (evAt u p h - q.eval u • h) := by
    intro u
    have e1 : evAt u p h = ∑ k ∈ p.support, u ^ k • p.coeff k h := by
      rw [evAt_apply, eval₂_eq_sum, Polynomial.sum_def, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← map_pow, RingHom.id_apply, ← Algebra.commutes, ← Algebra.smul_def]
      rfl
    rw [e1, hr]

    simp [eval_finsetSum, map_sum, eval_monomial, mul_comm]
  have hz : r = 0 := by
    refine eq_zero_of_infinite_isRoot r ?_
    refine Set.Infinite.mono (s := {b}ᶜ) ?_ (Set.finite_singleton b).infinite_compl
    intro u hu
    have hu' : u ≠ b := hu
    change r.eval u = 0
    rw [hev, H u hu', sub_self, map_zero]
  rw [← hev, hz, eval_zero]

theorem compLeft_smul_one {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (c : ℂ) (w : Fin n → V) :
    (c • (1 : Module.End ℂ V)).compLeft (Fin n) w = c • w := by
  funext i
  simp [LinearMap.compLeft_apply]

theorem tens_apply {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (hS : ScalChar X χ) (u : ℂ) (w : Fin n → X.V) :
    qdet (tensE X) u (u • w + om X w) =
      Formalism.QuantumDeterminants.capP χ (u - cn n) • ((u + 1) • w + om X w) := by
  have hq : qdet X.E u = Formalism.QuantumDeterminants.capP χ (u - cn n) • (1 : Module.End ℂ X.V) := by
    have := hS (u - cn n)
    rwa [show u - cn n + ((n : ℂ) - 1) / 2 = u by unfold cn; ring] at this
  have h := LinearMap.congr_fun (GlobalTheory.T.QuantumDeterminantTensor n X u) w
  rw [hq] at h
  simpa [Module.End.mul_apply, compLeft_smul_one] using h

theorem core {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (s : Fin n) (hS : ScalChar X χ)
    (hs : ∀ r, r ≠ s → χ r ≠ χ s) (g : Fin n → X.V)
    (h2 : om X (om X g - (χ s - cn n) • g) = (χ s - cn n) • (om X g - (χ s - cn n) • g)) :
    om X g - (χ s - cn n) • g = 0 := by
  set a : ℂ := χ s - cn n with ha
  set h : Fin n → X.V := om X g - a • g with hh
  set ct : ℂ → ℂ := fun u => ∏ t ∈ univ.erase s, (u - cn n + χ t) with hct
  have hc : ∀ u, Formalism.QuantumDeterminants.capP χ (u - cn n) = (u + a) * ct u := by
    intro u
    have := Finset.mul_prod_erase univ (fun t => u - cn n + χ t) (mem_univ s)
    simp only [Formalism.QuantumDeterminants.capP, hct]
    rw [← this, ha]
    ring_nf
  set q : ℂ[X] := (∏ t ∈ univ.erase s, (Polynomial.X - C (cn n) + C (χ t))) * (Polynomial.X + C (a + 1)) with hq
  have hqe : ∀ u, q.eval u = ct u * (u + (a + 1)) := by
    intro u
    simp [hq, hct, eval_prod]
  have hne : ∀ u, u ≠ -a → evAt u (qdetPoly (tensE X)) h = q.eval u • h := by
    intro u hu
    have hw : u + a ≠ 0 := fun e => hu (eq_neg_of_add_eq_zero_left e)
    have e := tens_apply X χ hS u h
    rw [h2, hc] at e
    rw [evAt_qdetPoly, hqe]
    have e1 : u • h + a • h = (u + a) • h := (add_smul _ _ _).symm
    have e2 : (u + 1) • h + a • h = (u + (a + 1)) • h := by rw [← add_smul]; ring_nf
    rw [e1, e2, map_smul, smul_smul, mul_assoc, ← smul_smul] at e
    exact smul_right_injective _ hw e
  have hb := cont _ q h (-a) hne
  rw [evAt_qdetPoly, hqe] at hb
  have hzero : qdet (tensE X) (-a) h = 0 := by
    have e := tens_apply X χ hS (-a) g
    rw [hc] at e
    have e0 : (-a) • g + om X g = h := by rw [hh, neg_smul]; abel
    rw [e0] at e
    rw [e]
    simp
  rw [hzero] at hb
  have hct0 : ct (-a) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.2 fun t ht => ?_
    have ht' : t ≠ s := Finset.ne_of_mem_erase ht
    have : -a - cn n + χ t = χ t - χ s := by rw [ha]; ring
    rw [this]
    exact sub_ne_zero.2 (hs t ht')
  have hfin : ct (-a) • h = 0 := by
    have : ct (-a) * (-a + (a + 1)) = ct (-a) := by ring
    rw [this] at hb
    exact hb.symm
  exact (smul_eq_zero.1 hfin).resolve_left hct0

theorem omScal : OmScal := by
  intro n X χ s hS hs f hf
  set T : Module.End ℂ (Fin n → X.V) := om X - (χ s - cn n) • (1 : Module.End ℂ (Fin n → X.V)) with hT
  have hTa : ∀ w, T w = om X w - (χ s - cn n) • w := fun w => by simp [hT]
  have key : ∀ k : ℕ, (T ^ (k + 1)) f = 0 → T f = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      intro hk
      refine ih ?_
      have h2 : T (T ((T ^ k) f)) = 0 := by
        rw [← hk, pow_succ' T (k + 1), pow_succ' T k]
        rfl
      have h3 := core X χ s hS hs ((T ^ k) f) (by
        rw [hTa] at h2
        rw [← hTa]
        exact sub_eq_zero.1 h2)
      rw [← hTa] at h3
      rw [pow_succ' T k]
      exact h3
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 hf
  have hk' : (T ^ (k + 1)) f = 0 := by
    rw [pow_succ' T k, Module.End.mul_apply]
    have : (T ^ k) f = 0 := hk
    rw [this, map_zero]
  have := key k hk'
  rw [hTa] at this
  exact sub_eq_zero.1 this

end GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaScalarStatement

section

@[expose] public section


theorem _root_.GlobalTheory.T.OmegaScalar : CompanionTheory.RgExh.Hk.OmScal := by
  first | exact @GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal | exact GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal | (intros; apply GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.omScal <;> assumption)
end
end

-- Source module: CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.HeckeAlgebraActions.InfinitesimalCharacterShift

section

@[expose] public section

namespace CompanionTheory.RgExh.Hk

theorem unitarity : Unit := UnitB.unit_of_dualFacts dual_module_facts

theorem reflection_symmetry : Reflect :=
  reflect_of' GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.OmegaScalar GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity

theorem forward_simple_module : FwdSimple :=
  forward_simple_of_tensor_facts GlobalTheory.T.QuantumDeterminantTensor GlobalTheory.T.HeckeBackwardStable dual_module_facts unitarity

theorem infinitesimal_character_shift : CompanionTheory.RgExh.StepChar := GlobalTheory.T.InfinitesimalCharacterStatement

theorem hecke_algebra_exhaustion : CompanionTheory.RgExh.Hecke :=
  hecke_of' GlobalTheory.T.QuantumDeterminantEquality GlobalTheory.T.InfinitesimalCharacterStatement GlobalTheory.T.CayleyHamiltonHk GlobalTheory.T.HeckeNonVanishing GlobalTheory.T.HeckeNonScalar GlobalTheory.T.HeckeBackward GlobalTheory.T.OmegaScalar
    forward_simple_module reflection_symmetry

end CompanionTheory.RgExh.Hk
end
end
