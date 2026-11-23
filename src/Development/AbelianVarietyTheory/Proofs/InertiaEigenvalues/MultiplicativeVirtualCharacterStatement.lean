module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MonodromyZeroOfWeilDeligneRepClassIff
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
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
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow
import Formalism.ConjugateSelfDual.Statement
public import Mathlib.RingTheory.Polynomial.Vieta
import ReciprocityTheory.GaloisValuations.GlobalA
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Mathlib.Tactic.Linter.Style

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowers

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.TracePowCharpoly

open Polynomial Finset

theorem newton_fn {σ : Type} [Fintype σ] (f : σ → ℂ) (k : ℕ) :
    (k : ℂ) * (univ.val.map f).esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k,
        (-1) ^ a.1 * (univ.val.map f).esymm a.1 * ∑ i, f i ^ a.2 := by
  have h := congrArg (MvPolynomial.aeval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)

  simpa only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
  MvPolynomial.aeval_esymm_eq_multiset_esymm, MvPolynomial.psum, MvPolynomial.aeval_X] using h

theorem newton_multiset (s : Multiset ℂ) (k : ℕ) :
    (k : ℂ) * s.esymm k = (-1) ^ (k + 1) *
      ∑ a ∈ antidiagonal k with a.1 < k, (-1) ^ a.1 * s.esymm a.1 * (s.map (· ^ a.2)).sum := by
  have hs : s = (univ : Finset (Fin s.toList.length)).val.map (fun i => s.toList.get i) := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have h := newton_fn (fun i : Fin s.toList.length => s.toList.get i) k
  rw [← hs] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  have e : ∀ n : ℕ, (s.map (· ^ n)).sum = ∑ i : Fin s.toList.length, s.toList.get i ^ n := by
    intro n
    conv_lhs => rw [hs]
    rw [Multiset.map_map]
    rfl
  exact (e a.2).symm

theorem esymm_eq_of_psum_eq (s t : Multiset ℂ) (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    ∀ k, s.esymm k = t.esymm k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [Multiset.esymm, Multiset.powersetCard_zero_left]
    · have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
      apply mul_left_cancel₀ hk0
      rw [newton_multiset, newton_multiset]
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [ih a.1 (Finset.mem_filter.mp ha).2, h a.2]

theorem prod_eq_of_psum_eq (s t : Multiset ℂ) (hc : Multiset.card s = Multiset.card t)
    (h : ∀ k, (s.map (· ^ k)).sum = (t.map (· ^ k)).sum) :
    (s.map (fun a => X - C a)).prod = (t.map (fun a => X - C a)).prod := by
  ext k
  by_cases hk : k ≤ Multiset.card s
  · rw [Multiset.prod_X_sub_C_coeff s hk, Multiset.prod_X_sub_C_coeff t (hc ▸ hk), hc,
      esymm_eq_of_psum_eq s t h]
  · push_neg at hk
    rw [coeff_eq_zero_of_natDegree_lt, coeff_eq_zero_of_natDegree_lt]
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega
    · rw [natDegree_multiset_prod_X_sub_C_eq_card]; omega

end GlobalTheory.TracePowCharpoly

namespace GlobalTheory.TracePowCharpoly

open Polynomial

theorem trace_pow_eq_sum_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) (k : ℕ) :
    LinearMap.trace ℂ V (f ^ k) =
      ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (· ^ k)).sum := by
  classical
  rw [LinearMap.trace_eq_matrix_trace ℂ (Module.finBasis ℂ V), ← GlobalTheory.CharpolyPow.roots_charpoly_pow,
    ← Matrix.trace_eq_sum_roots_charpoly]
  congr 1
  induction k with
  | zero => simp [LinearMap.toMatrix_one]
  | succ n ih => rw [pow_succ, LinearMap.toMatrix_mul, ih, pow_succ]

theorem charpoly_eq_prod_roots {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f : Module.End ℂ V) :
    f.charpoly = ((LinearMap.toMatrix (Module.finBasis ℂ V) (Module.finBasis ℂ V) f).charpoly.roots.map
        (fun a => X - C a)).prod := by
  classical
  rw [← LinearMap.charpoly_toMatrix f (Module.finBasis ℂ V)]
  exact (IsAlgClosed.splits _).eq_prod_roots_of_monic (Matrix.charpoly_monic _)

theorem charpoly_eq_of_trace_pow_eq : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  intro V V' _ _ _ _ _ _ f g h
  have hdim : Module.finrank ℂ V = Module.finrank ℂ V' := by
    have h0 := h 0
    simp only [pow_zero, LinearMap.trace_one] at h0
    exact_mod_cast h0
  rw [charpoly_eq_prod_roots f, charpoly_eq_prod_roots g]
  apply prod_eq_of_psum_eq
  · rw [GlobalTheory.CharpolyPow.card_roots_charpoly, GlobalTheory.CharpolyPow.card_roots_charpoly, hdim]
  · intro k
    rw [← trace_pow_eq_sum_roots, ← trace_pow_eq_sum_roots, h k]

end GlobalTheory.TracePowCharpoly
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyEqOfTracePowersStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.charpoly_eq_of_trace_powers : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V'] (f : Module.End ℂ V) (g : Module.End ℂ V'), (∀ k : ℕ, LinearMap.trace ℂ V (f ^ k) = LinearMap.trace ℂ V' (g ^ k)) → f.charpoly = g.charpoly := by
  first | exact @GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | exact GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq | (intros; apply GlobalTheory.TracePowCharpoly.charpoly_eq_of_trace_pow_eq <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacter

section

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

namespace GlobalTheory.WeilDeligne.VirtualTrace

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def listSum (h : IsPlaceOver A w) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    Σ n : ℕ, WDRep h (Fin n → ℂ) :=
  L.foldr (fun x s => WD.std (x.2.sum s.2)) ⟨0, WDRep.diag h (ι := Fin 0) fun i => i.elim0⟩

theorem mk_listSum_cons (x : Σ n : ℕ, WDRep h (Fin n → ℂ)) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    WD.mk (listSum h (x :: L)).2 = WD.lpSum (WD.mk x.2) (WD.mk (listSum h L).2) := by
  rw [WD.lpSum_mk]
  exact WD.sound (WD.iso_std _).symm

theorem trace_std {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (a : WDRep h V) (σ : Weil h) (k : ℕ) :
    LinearMap.trace ℂ _ ((WD.std a).2.ρ σ ^ k) = LinearMap.trace ℂ V (a.ρ σ ^ k) := by
  show LinearMap.trace ℂ _ (((Module.finBasis ℂ V).equivFun.conjAlgEquiv ℂ (a.ρ σ)) ^ k) = _
  rw [← map_pow]
  exact LinearMap.trace_conj' _ _

theorem trace_listSum (σ : Weil h) (k : ℕ) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    LinearMap.trace ℂ _ ((listSum h L).2.ρ σ ^ k) =
      (L.map fun x => LinearMap.trace ℂ _ (x.2.ρ σ ^ k)).sum := by
  induction L with
  | nil =>
    simp only [List.map_nil, List.sum_nil]
    have : Subsingleton (Fin (listSum h []).1 → ℂ) := by
      show Subsingleton (Fin 0 → ℂ); infer_instance
    have hz : (listSum h []).2.ρ σ ^ k = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    rw [hz, map_zero]
  | cons x L ih =>
    simp only [List.map_cons, List.sum_cons]
    refine (trace_std (x.2.sum (listSum h L).2) σ k).trans ?_
    rw [WDRep.sum_ρ, ← ih]
    have : ((x.2.ρ σ).prodMap ((listSum h L).2.ρ σ)) ^ k = (x.2.ρ σ ^ k).prodMap ((listSum h L).2.ρ σ ^ k) :=
      (map_pow (LinearMap.prodMapRingHom ℂ _ _) (x.2.ρ σ, (listSum h L).2.ρ σ) k).symm
    rw [this, LinearMap.trace_prodMap']

theorem map_lpZero {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) : f (WD.lpZero (h := h)) = 1 := by
  have hzero := hf (WD.lpZero (h := h)) (WD.lpZero (h := h))
  rw [WD.lpSum_zero] at hzero
  exact mul_left_cancel (hzero.symm.trans (mul_one _).symm)

theorem map_listSum {M : Type} [CommGroup M] (f : WD h → M)
    (hf : ∀ x y, f (x.lpSum y) = f x * f y) (L : List (Σ n : ℕ, WDRep h (Fin n → ℂ))) :
    f (WD.mk (listSum h L).2) = (L.map fun x => f (WD.mk x.2)).prod := by
  induction L with
  | nil => exact map_lpZero f hf
  | cons x L ih => rw [mk_listSum_cons, hf, ih, List.map_cons, List.prod_cons]

theorem prod_flatMap_replicate {ι α M : Type} [CommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).prod = ∏ i ∈ s, g (x i) ^ n i := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).prod =
      (l.map fun i => g (x i) ^ n i).prod := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.prod_append, ih, List.map_replicate, List.prod_replicate]
  rw [key, Finset.prod_map_toList]

theorem sum_flatMap_replicate {ι α M : Type} [AddCommMonoid M] (s : Finset ι) (n : ι → ℕ)
    (x : ι → α) (g : α → M) :
    ((s.toList.flatMap fun i => List.replicate (n i) (x i)).map g).sum = ∑ i ∈ s, n i • g (x i) := by
  have key : ∀ l : List ι, ((l.flatMap fun i => List.replicate (n i) (x i)).map g).sum =
      (l.map fun i => n i • g (x i)).sum := by
    intro l
    induction l with
    | nil => simp
    | cons i l ih => simp [List.flatMap_cons, List.sum_append, ih, List.map_replicate, List.sum_replicate]
  rw [key, Finset.sum_map_toList]

end GlobalTheory.WeilDeligne.VirtualTrace


open GlobalTheory.WeilDeligne.VirtualTrace in
theorem GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero :
    ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ),
    (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) →
    ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ),
    (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) →
    ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  intro E Ω _ _ _ _ _ A w h f hf1 hf2 ι _ d a c hc
  classical
  let x : ι → Σ n : ℕ, WDRep h (Fin n → ℂ) := fun i => ⟨d i, a i⟩
  let L : (ι → ℕ) → List (Σ n : ℕ, WDRep h (Fin n → ℂ)) := fun n =>
    (Finset.univ : Finset ι).toList.flatMap fun i => List.replicate (n i) (x i)
  have hfL : ∀ n, f (WD.mk (listSum h (L n)).2) = ∏ i, f (WD.mk (a i)) ^ n i := fun n => by
    rw [map_listSum f hf1]
    exact prod_flatMap_replicate _ n x (fun y => f (WD.mk y.2))
  have htL : ∀ n σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L n)).2.ρ σ ^ k) =
      ∑ i, (n i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ ^ k) := fun n σ k => by
    rw [trace_listSum]
    rw [sum_flatMap_replicate _ n x (fun y => LinearMap.trace ℂ _ (y.2.ρ σ ^ k))]
    simp only [nsmul_eq_mul, x]
  have hcc : ∀ i, ((c i : ℤ) : ℂ) = (((c i).toNat : ℕ) : ℂ) - (((-c i).toNat : ℕ) : ℂ) := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    push_cast; ring
  have htr : ∀ σ (k : ℕ), LinearMap.trace ℂ _ ((listSum h (L fun i => (c i).toNat)).2.ρ σ ^ k) =
      LinearMap.trace ℂ _ ((listSum h (L fun i => (-c i).toNat)).2.ρ σ ^ k) := fun σ k => by
    rw [htL, htL, ← sub_eq_zero, ← Finset.sum_sub_distrib]
    have := hc (σ ^ k)
    simp only [map_pow, hcc] at this
    rw [← this]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hPQ : f (WD.mk (listSum h (L fun i => (c i).toNat)).2) =
      f (WD.mk (listSum h (L fun i => (-c i).toNat)).2) :=
    hf2 _ _ fun σ => by
      rw [WD.charPol_mk, WD.charPol_mk]
      exact GlobalTheory.T.charpoly_eq_of_trace_powers _ _ _ _ (htr σ)
  rw [hfL, hfL] at hPQ
  have hz : ∀ i, f (WD.mk (a i)) ^ c i =
      f (WD.mk (a i)) ^ (c i).toNat * (f (WD.mk (a i)) ^ (-c i).toNat)⁻¹ := fun i => by
    conv_lhs => rw [← Int.toNat_sub_toNat_neg (c i)]
    rw [zpow_sub, zpow_natCast, zpow_natCast]
  simp only [hz, Finset.prod_mul_distrib, Finset.prod_inv_distrib, hPQ, mul_inv_cancel]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MultiplicativeVirtualCharacterStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne

theorem _root_.GlobalTheory.T.multiplicative_virtual_character : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (f : WD h → ℂˣ), (∀ x y, f (x.lpSum y) = f x * f y) → (∀ x y, (∀ σ, x.charPol σ = y.charPol σ) → f x = f y) → ∀ (ι : Type) [Fintype ι] (d : ι → ℕ) (a : ∀ i, WDRep h (Fin (d i) → ℂ)) (c : ι → ℤ), (∀ σ, ∑ i, (c i : ℂ) * LinearMap.trace ℂ (Fin (d i) → ℂ) ((a i).ρ σ) = 0) → ∏ i, f (WD.mk (a i)) ^ c i = 1 := by
  first | exact @GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | exact GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero | (intros; apply GlobalTheory.WeilDeligne.VirtualTrace.prod_zpow_eq_one_of_trace_zero <;> assumption)
end
end
