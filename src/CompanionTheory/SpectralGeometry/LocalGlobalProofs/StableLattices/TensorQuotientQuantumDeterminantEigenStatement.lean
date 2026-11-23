module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.IsSimpleTriv
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.InfinitesimalCharacterPaths.TensDecomp
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.KeepsMul
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
public import Mathlib.Algebra.Module.Submodule.LinearMap
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HasCharSub
public import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernel

section

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

namespace GlobalTheory.CompanionTheory.RgTransport

theorem exists_joint_kernel_finset {V : Type} [AddCommGroup V] [Module ℂ V]
    (I : Submodule ℂ V) (hI : I ≠ ⊥) (D : ℂ → Module.End ℂ V)
    (hcomm : ∀ Y Y', Commute (D Y) (D Y'))
    (hstab : ∀ Y, ∀ x ∈ I, D Y x ∈ I)
    (hnil : ∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) (F : Finset ℂ) :
    ∃ w ∈ I, w ≠ 0 ∧ ∀ Y ∈ F, D Y w = 0 := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff I).1 hI
    exact ⟨x, hx, hx0, by simp⟩
  | insert a F _ ih =>
    obtain ⟨x, hx, hx0, hF⟩ := ih
    have hex : ∃ N : ℕ, (D a ^ N) x = 0 := hnil a x hx
    have hN := Nat.find_spec hex
    have hmin := fun m => Nat.find_min hex (m := m)
    set N := Nat.find hex with hNdef
    have hpos : N ≠ 0 := by
      intro h0
      rw [h0] at hN
      exact hx0 (by simpa using hN)
    obtain ⟨M, hM⟩ := Nat.exists_eq_succ_of_ne_zero hpos
    have hiter : ∀ k : ℕ, (D a ^ k) x ∈ I := by
      intro k
      induction k with
      | zero => simpa using hx
      | succ k ihk =>
        rw [pow_succ', Module.End.mul_apply]
        exact hstab a _ ihk
    refine ⟨(D a ^ M) x, hiter M, hmin M (by omega), ?_⟩
    intro Y hY
    rcases Finset.mem_insert.1 hY with rfl | hY
    · rw [← Module.End.mul_apply, ← pow_succ']
      rw [hM] at hN
      exact hN
    · have hc : Commute (D Y) (D a ^ M) := (hcomm Y a).pow_right M
      rw [← Module.End.mul_apply, hc.eq, Module.End.mul_apply, hF Y hY, map_zero]

theorem exists_joint_kernel_polynomial_family :
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ →
      ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) →
      (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) →
      ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) →
      ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  intro V _ _ I hI D hcomm hstab hnil l c hD
  classical
  let F : Finset ℂ := (Finset.range l).image (fun n : ℕ => (n : ℂ))
  have hcard : F.card = l := by
    simpa using Finset.card_image_of_injective (Finset.range l)
      (Nat.cast_injective (R := ℂ))
  obtain ⟨w, hw, hw0, hF⟩ := exists_joint_kernel_finset I hI D hcomm hstab hnil F
  refine ⟨w, hw, hw0, fun Y => ?_⟩
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (D Y w)).1 fun φ => ?_
  let p : Polynomial ℂ :=
    ∑ j ∈ Finset.range l, Polynomial.C (φ (c j w)) * Polynomial.X ^ j
  have heval : ∀ Z : ℂ, p.eval Z = φ (D Z w) := by
    intro Z
    rw [hD Z]

    simp only [p, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_pow, Polynomial.eval_X, LinearMap.sum_apply, LinearMap.smul_apply,
    map_sum, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  have hdeg : p.degree < (F.card : ℕ) := by
    rw [hcard]
    refine (Polynomial.degree_sum_le _ _).trans_lt ?_
    refine (Finset.sup_lt_iff (WithBot.bot_lt_coe l)).2 fun j hj => ?_
    refine (Polynomial.degree_C_mul_X_pow_le j _).trans_lt ?_
    exact WithBot.coe_lt_coe.2 (Finset.mem_range.1 hj)
  have hp : p = 0 :=
    Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero F hdeg
      (fun Z hZ => by rw [heval, hF Z hZ, map_zero])
  rw [← heval, hp, Polynomial.eval_zero]

end GlobalTheory.CompanionTheory.RgTransport
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CommutingLocallyNilpotentCommonKernelStatement

section

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

theorem _root_.GlobalTheory.T.commuting_locally_nilpotent_common_kernel : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (I : Submodule ℂ V), I ≠ ⊥ → ∀ (D : ℂ → Module.End ℂ V), (∀ Y Y', Commute (D Y) (D Y')) → (∀ Y, ∀ x ∈ I, D Y x ∈ I) → (∀ Y, ∀ x ∈ I, ∃ N : ℕ, (D Y ^ N) x = 0) → ∀ (l : ℕ) (c : ℕ → Module.End ℂ V), (∀ Y, D Y = ∑ j ∈ Finset.range l, Y ^ j • c j) → ∃ w ∈ I, w ≠ 0 ∧ ∀ Y, D Y w = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | exact GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family | (intros; apply GlobalTheory.CompanionTheory.RgTransport.exists_joint_kernel_polynomial_family <;> assumption)
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigen

section

@[expose] public section

noncomputable section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

namespace GlobalTheory.CompanionTheory.RgTransport.Raise

theorem exists_capelliPoly_eq_sum {m : ℕ} (χ : Fin m → ℂ) :
    ∃ a : ℕ → ℂ, ∀ Y : ℂ, Formalism.QuantumDeterminants.capP χ Y = ∑ j ∈ Finset.range (m + 1), Y ^ j * a j := by
  let p : Polynomial ℂ := ∏ s : Fin m, (Polynomial.X + Polynomial.C (χ s))
  have hd : p.natDegree ≤ m := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc _ ≤ ∑ _s : Fin m, 1 := Finset.sum_le_sum fun s _ => (Polynomial.natDegree_X_add_C _).le
      _ = m := by simp
  refine ⟨p.coeff, fun Y => ?_⟩
  have e : Formalism.QuantumDeterminants.capP χ Y = p.eval Y := by
    simp [p, Formalism.QuantumDeterminants.capP, Polynomial.eval_prod]
  rw [e, Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd)]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem exists_raised : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ →
    ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E →
    ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 →
    ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ,
      qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  intro hS hT m M χ hM V _ _ E hE Φ hΦ hne
  have hsup := hT m M χ hM
  obtain ⟨r, hr⟩ : ∃ r, ¬ stepSub M (χ r) ≤ LinearMap.ker Φ := by
    by_contra h
    push Not at h
    have h' : (⊤ : Submodule ℂ (Fin m → M.V)) ≤ LinearMap.ker Φ := hsup ▸ iSup_le h
    exact hne (LinearMap.ker_eq_top.1 (top_le_iff.1 h'))
  obtain ⟨N, hN⟩ := hS m M χ r hM
  let f : (step M (χ r)).V →ₗ[ℂ] V := Φ ∘ₗ (stepSub M (χ r)).subtype
  have hf : ∀ a b x, f ((step M (χ r)).E a b x) = E a b (f x) := fun a b x => hΦ a b x.1
  let D : ℂ → Module.End ℂ V := fun Y =>
    qdet E (Y + ((m : ℂ) - 1) / 2) - Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • (1 : Module.End ℂ V)
  have hI : LinearMap.range f ≠ ⊥ := by
    intro h0
    refine hr fun x hx => ?_
    have : f ⟨x, hx⟩ ∈ LinearMap.range f := ⟨_, rfl⟩
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hsh : ∀ Y x, f ((qdet (step M (χ r)).E (Y + ((m : ℂ) - 1) / 2) -
      Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • (1 : Module.End ℂ (step M (χ r)).V)) x) = D Y (f x) := fun Y x =>
    shift_lin f _ _ (fun y => qdet_lin f (step M (χ r)).E E hf _ y) _ x
  have hcomm : ∀ Y Y', Commute (D Y) (D Y') := by
    intro Y Y'
    have h0 : Commute (qdet E (Y + ((m : ℂ) - 1) / 2)) (qdet E (Y' + ((m : ℂ) - 1) / 2)) :=
      by
        unfold qdet qminor
        refine Commute.sum_right _ _ _ fun σ _ => ?_
        refine Commute.mul_right (Int.cast_commute _ _).symm ?_
        refine Commute.list_prod_right _ _ fun x hx => ?_
        rw [List.mem_ofFn] at hx
        obtain ⟨k, rfl⟩ := hx
        unfold Tm
        refine Commute.add_right ?_ (qDetCentral _ m E hE _ _ _)
        split_ifs
        · exact Algebra.commute_algebraMap_right _ _
        · exact Commute.zero_right _
    refine Commute.sub_left (Commute.sub_right h0 ((Commute.one_right _).smul_right _)) ?_
    exact ((Commute.one_left _).smul_left _).sub_right ((Commute.one_left _).smul_left _ |>.smul_right _)
  have hst : ∀ Y, ∀ x ∈ LinearMap.range f, D Y x ∈ LinearMap.range f := by
    rintro Y _ ⟨x, rfl⟩
    exact ⟨_, hsh Y x⟩
  have hnil : ∀ Y, ∀ x ∈ LinearMap.range f, ∃ k : ℕ, (D Y ^ k) x = 0 := by
    rintro Y _ ⟨x, rfl⟩
    refine ⟨N, ?_⟩
    have e := pow_lin f _ (D Y) (hsh Y) N x
    rw [hN Y] at e
    simpa using e.symm
  let t : ℕ → Fin m → Fin m → Polynomial (Module.End ℂ V) := fun k a b =>
    (if a = b then Polynomial.X + Polynomial.C (algebraMap ℂ (Module.End ℂ V) (((m : ℂ) - 1) / 2 - k)) else 0) + Polynomial.C (E a b)
  let p : Polynomial (Module.End ℂ V) := ∑ σ : Equiv.Perm (Fin m), Polynomial.C ((Equiv.Perm.sign σ : ℤ) : Module.End ℂ V) * (List.ofFn fun k : Fin m => t k (σ k) k).prod
  have ht : ∀ k a b, (t k a b).natDegree ≤ 1 := by
    intro k a b
    dsimp [t]
    split_ifs
    · exact (Polynomial.natDegree_add_le _ _).trans (max_le ((Polynomial.natDegree_add_le _ _).trans (max_le Polynomial.natDegree_X_le (by rw [Polynomial.natDegree_C]; omega))) (by simp))
    · simp
  have hp : p.natDegree ≤ m := by
    dsimp [p]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun σ _ => (Polynomial.natDegree_C_mul_le _ _).trans ?_
    refine (Polynomial.natDegree_list_prod_le _).trans ?_
    rw [List.map_ofFn, List.sum_ofFn]
    calc _ ≤ ∑ _k : Fin m, 1 := Finset.sum_le_sum fun k _ => ht _ _ _
      _ = m := by simp
  let ev (Y : ℂ) : Polynomial (Module.End ℂ V) →+* Module.End ℂ V :=
    Polynomial.eval₂RingHom' (RingHom.id _) (algebraMap ℂ _ Y) (fun a => (Algebra.commutes Y a).symm)
  have hc : ∀ Y, qdet E (Y + ((m : ℂ) - 1) / 2) = ∑ j ∈ Finset.range (m + 1), Y ^ j • p.coeff j := by
    intro Y
    have he : ev Y p = qdet E (Y + ((m : ℂ) - 1) / 2) := by
      dsimp [p]
      unfold qdet qminor
      rw [map_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [map_mul, map_list_prod, List.map_ofFn]
      congr 1
      · simp [ev]
      · congr 1
        congr 1
        funext k
        simp only [Function.comp_apply]
        dsimp [t, Tm]
        split_ifs <;> change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ _ Y) _ = _ <;>
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [← he]
    change Polynomial.eval₂ (RingHom.id _) (algebraMap ℂ _ Y) p = _
    rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [RingHom.id_apply, ← map_pow]
    rw [Algebra.smul_def]
    exact (Algebra.commutes _ _).symm
  let c := p.coeff
  obtain ⟨a, ha⟩ := exists_capelliPoly_eq_sum (χ + Pi.single r 1)
  have hD : ∀ Y, D Y = ∑ j ∈ Finset.range (m + 1), Y ^ j • (c j - a j • (1 : Module.End ℂ V)) := by
    intro Y
    have h1 := hc Y
    simp only [D, h1, ha Y, c, smul_sub, Finset.sum_sub_distrib, Finset.sum_smul, mul_smul]
  obtain ⟨w, hw, hw0, hwD⟩ := GlobalTheory.T.commuting_locally_nilpotent_common_kernel _ hI D hcomm hst hnil (m + 1) _ hD
  obtain ⟨x, rfl⟩ := hw
  refine ⟨r, f x, ⟨_, rfl⟩, hw0, fun Y => ?_⟩
  have h2 := hwD Y
  simpa [D, sub_eq_zero] using h2

end GlobalTheory.CompanionTheory.RgTransport.Raise
end
end
end

-- Source module: CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.TensorQuotientQuantumDeterminantEigenStatement

section

@[expose] public section

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.J Formalism.REAL ReciprocityTheory.ChartRestriction.DS GlobalTheory.SmGL GlobalTheory.CompanionTheory.RgTransport

theorem _root_.GlobalTheory.T.tensor_quotient_quantum_determinant_eigen : StepChar → TensDecomp → ∀ {m : ℕ} (M : GMod m) (χ : Fin m → ℂ), HasChar M χ → ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin m → Fin m → Module.End ℂ V), GlRel E → ∀ Φ : (Fin m → M.V) →ₗ[ℂ] V, (∀ a b u, Φ (tensE M a b u) = E a b (Φ u)) → Φ ≠ 0 → ∃ r, ∃ w ∈ LinearMap.range Φ, w ≠ 0 ∧ ∀ Y : ℂ, qdet E (Y + ((m : ℂ) - 1) / 2) w = Formalism.QuantumDeterminants.capP (χ + Pi.single r 1) Y • w := by
  first | exact @GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | exact GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised | (intros; apply GlobalTheory.CompanionTheory.RgTransport.Raise.exists_raised <;> assumption)
end
end
