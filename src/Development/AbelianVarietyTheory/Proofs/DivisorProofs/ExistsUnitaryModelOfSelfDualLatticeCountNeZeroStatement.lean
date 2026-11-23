module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
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
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMulStarEqOfNormOneUnramifiedQuadratic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocallyCompactOfComplete
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Divisors.SimpleTwistedTraceFormulaStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtensionStatement
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasis

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat.ModelOfBasis

variable {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K)

theorem herm_sum_left (x z : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x (∑ k ∈ s, f k) z = ∑ k ∈ s, B.herm x (f k) z := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm

  rw [Finset.mul_sum, Finset.sum_mul, map_sum]

theorem herm_sum_right (x y : B.A) {ι : Type} (s : Finset ι) (f : ι → B.A) :
    B.herm x y (∑ k ∈ s, f k) = ∑ k ∈ s, B.herm x y (f k) := by
  unfold GlobalTheory.UnitLemma.InvAlg.herm

  rw [map_sum, Finset.mul_sum, map_sum]

theorem herm_eq_sum {n : ℕ} (x : B.A) (b : Module.Basis (Fin n) K.E B.A)
    (hb : ∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) (y z : B.A) :
    B.herm x y z = ∑ k, b.repr y k * K.c (b.repr z k) := by
  conv_lhs => rw [← b.sum_repr y, ← b.sum_repr z]
  rw [herm_sum_left]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [herm_sum_right, Finset.sum_eq_single k]
  · rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_pos rfl]; ring
  · intro l _ hl
    rw [GlobalTheory.UnitLemma.Basic.herm_smul_left, GlobalTheory.UnitLemma.Basic.herm_smul_right, hb, if_neg (Ne.symm hl)]; ring
  · intro h; exact absurd (Finset.mem_univ k) h

end GlobalTheory.KapLat.ModelOfBasis

open GlobalTheory.KapLat.ModelOfBasis in
theorem GlobalTheory.KapLat.exists_model_of_orthonormal_basis :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hbr n B u x hu b hb
  let ψ : B.A ≃+ (Fin n → w.adicCompletion E) :=
    b.equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hψ : ∀ y k, ψ y k = e (b.repr y k) := fun y k => rfl
  have hstd : ∀ y z, stdH w (ψ y) (ψ z) = e (B.herm x y z) := by
    intro y z

    rw [herm_eq_sum B x b hb, map_sum]
    unfold stdH
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hψ, hψ, map_mul, hbr.1]
  let M : Matrix (Fin n) (Fin n) (w.adicCompletion E) := Matrix.of fun k i => e (b.repr (u * b i) k)
  have hM : ∀ y, ψ (u * y) = M *ᵥ ψ y := by
    intro y
    funext k
    have hy : u * y = ∑ i, b.repr y i • (u * b i) := by
      conv_lhs => rw [← b.sum_repr y]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_smul_comm _ _ _

    rw [hψ, hy, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, map_sum]
    simp only [Matrix.mulVec, dotProduct, M, Matrix.of_apply, hψ, map_smul, Finsupp.smul_apply, smul_eq_mul,
      map_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hunit : cT (cj w) M * M = 1 := by
    ext i j
    have h := hstd (u * b j) (u * b i)
    rw [← GlobalTheory.UnitLemma.Basic.herm_norm, hu, mul_one, hb] at h
    simp only [stdH, hψ] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [cT, Matrix.transpose_apply, Matrix.map_apply, M, Matrix.of_apply]
    rw [Finset.sum_congr rfl fun k _ => mul_comm _ _, h]
    by_cases hij : i = j
    · subst hij; simp
    · rw [if_neg (Ne.symm hij), if_neg hij, map_zero]
  have hunit' : M * cT (cj w) M = 1 := mul_eq_one_comm.mp hunit
  let γ : GLw n w := ⟨M, cT (cj w) M, hunit', hunit⟩
  refine ⟨γ, ?_, ψ, ?_, hM, hstd⟩
  · unfold UL
    rw [if_neg hw]
    show cT (cj w) M * 1 * M = 1
    rw [Matrix.mul_one, hunit]
  · intro c y
    funext k
    rw [hψ, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, hψ, smul_eq_mul]
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasisStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w →
    ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e →
    ∀ (n : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), u * B.σ u = 1 →
    ∀ b : Module.Basis (Fin n) K.E B.A, (∀ i j, B.herm x (b i) (b j) = if i = j then 1 else 0) →
    ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_orthonormal_basis | exact GlobalTheory.KapLat.exists_model_of_orthonormal_basis | (intros; apply GlobalTheory.KapLat.exists_model_of_orthonormal_basis <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramified

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

namespace GlobalTheory.UnitLemma

theorem UQ.norm_of_fixed_unit {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E]
    [NormedAlgebra F E] [StarRing E] [GlobalTheory.JR.Unram F E] (w w' : E) (hs : star w = w) (h1 : ‖w‖ ≤ 1)
    (h1' : ‖w'‖ ≤ 1) (hww : w * w' = 1) : ∃ v : E, v * star v = w := by
  obtain ⟨ζ, -, hζ⟩ := GlobalTheory.NormUnits.exists_far_unit F E
  obtain ⟨a, ha⟩ := GlobalTheory.NormUnits.fixed_mem_range F E ζ hζ w hs
  have hprod : ‖w‖ * ‖w'‖ = 1 := by rw [← norm_mul, hww, norm_one]
  have hwn : ‖w‖ = 1 := by
    refine le_antisymm h1 ?_
    by_contra h
    push_neg at h
    have : ‖w‖ * ‖w'‖ < 1 :=
      calc ‖w‖ * ‖w'‖ ≤ ‖w‖ * 1 := by gcongr
        _ < 1 := by simpa using h
    linarith
  have han : ‖a‖ = 1 := by rw [← norm_algebraMap' E a, ha, hwn]
  obtain ⟨v, hv⟩ := GlobalTheory.NormUnits.norm_onto_units F E a han
  exact ⟨v, by rw [hv, ha]⟩

theorem UQ.unit_fixed_is_norm : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  intro K t ht hct
  obtain ⟨F, nF, nE, hE, nA, st, hU, hst, hball⟩ := K.exists_unram
  have hmul : ∀ x y : K.E, @HMul.hMul K.E K.E K.E (@instHMul K.E nE.toMul) x y = x * y := by
    intro x y; rw [← hE]
  have hone : @OfNat.ofNat K.E 1 (@One.toOfNat1 K.E nE.toOne) = 1 := by rw [← hE]
  obtain ⟨u, rfl⟩ := ht
  have hww : algebraMap K.O K.E u * algebraMap K.O K.E (u⁻¹ : K.Oˣ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  obtain ⟨v, hv⟩ := @UQ.norm_of_fixed_unit F K.E nF nE nA st hU (algebraMap K.O K.E u)
    (algebraMap K.O K.E (u⁻¹ : K.Oˣ)) (by rw [hst]; exact hct) ((hball _).2 ⟨u, rfl⟩) ((hball _).2 ⟨_, rfl⟩)
    (by rw [hmul, hone]; exact hww)
  refine ⟨v, ?_⟩
  rw [← hst, ← hmul]; exact hv

end GlobalTheory.UnitLemma
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramifiedStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.fixed_integral_unit_eq_norm_unramified : ∀ (K : GlobalTheory.UnitLemma.UQ) (t : K.O), IsUnit t → K.c (algebraMap K.O K.E t) = algebraMap K.O K.E t →
    ∃ v : K.E, v * K.c v = algebraMap K.O K.E t := by
  first | exact @GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | exact GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm | (intros; apply GlobalTheory.UnitLemma.UQ.unit_fixed_is_norm <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZero

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

theorem exists_orthonormal_of_selfDual (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V]
    [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z) (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (L : Submodule K.O V) (hfg : L.FG)
    (hsp : Submodule.span K.E (L : Set V) = ⊤) (hsd : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  have key : ∀ k, k ≤ Module.finrank K.E V → ∃ f : Fin k → V, (∀ i, f i ∈ L) ∧
      (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfo, hfu⟩ := ih (by omega)
      obtain ⟨y, hyL, hyo, hyu⟩ := GlobalTheory.T.selfDual_lattice_orthogonal_unit_norm_extension K V h hadd hsmul hsym L hfg hsp hsd k f hfL hfo hfu (by omega)
      refine ⟨Fin.snoc f y, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyL
        | cast i => simpa using hfL i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j => simpa using hyo j
        | cast i =>
          induction j using Fin.lastCases with
          | last => simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hsym, hyo i, map_zero]
          | cast j =>
            simp only [Fin.snoc_castSucc]
            exact hfo i j fun e => hij (by rw [e])
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyu
        | cast i => simpa using hfu i
  obtain ⟨f, -, hfo, hfu⟩ := key _ le_rfl
  choose t ht hft using hfu
  choose v hv using fun i => GlobalTheory.T.fixed_integral_unit_eq_norm_unramified K (t i) (ht i) (by rw [← hft, ← hsym])
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym, hsmul, map_mul, hsym z y]
  have ht0 : ∀ i, algebraMap K.O K.E (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (ht i).ne_zero
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i h0
    apply ht0 i
    rw [← hv i, h0, zero_mul]
  let g : Fin (Module.finrank K.E V) → V := fun i => (v i)⁻¹ • f i
  have hg : ∀ i j, h (g i) (g j) = if i = j then 1 else 0 := by
    intro i j
    simp only [g, hsmul, hsmul2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hft, ← hv i, map_inv₀]
      have : K.c (v i) ≠ 0 := by simpa using hv0 i
      field_simp
      exact div_self (hv0 i)
    · rw [if_neg hij, hfo i j hij, mul_zero, mul_zero]
  let φ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z
      map_add' := fun y y' => hadd y y' z
      map_smul' := fun a y => by simp [hsmul] }
  have hli : LinearIndependent K.E g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrArg (φ (g i)) hc

    simp only [map_sum, map_smul, map_zero] at this
    simpa [φ, hg] using this
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge, fun i j => ?_⟩
  rw [Module.Basis.mk_apply, Module.Basis.mk_apply]
  exact hg i j

theorem X_nonempty_of_N_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (hN : B.N x ≠ 0) :
    (B.X x).Nonempty := by
  by_contra hX
  rw [Set.not_nonempty_iff_eq_empty] at hX
  apply hN
  haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) :=
    ⟨fun o => by
      induction o using Quot.ind with
      | mk L => exact Set.eq_empty_iff_forall_notMem.1 hX L.1 L.2⟩
  unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
  exact finsum_of_isEmpty _

theorem exists_model_of_N_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hB n Q B u x hF hn hσx _ hN
  obtain ⟨L, hlat, -, hsd⟩ := X_nonempty_of_N_ne_zero B x hN
  obtain ⟨b, hb⟩ := exists_orthonormal_of_selfDual K B.A (B.herm x)
    (fun y y' z => by unfold GlobalTheory.UnitLemma.InvAlg.herm; rw [mul_add, add_mul, map_add (f := _)])
    (fun a y z => GlobalTheory.UnitLemma.Basic.herm_smul_left B x y z a)
    (fun y z => GlobalTheory.UnitLemma.Basic.herm_symm B x hσx y z) L hlat.1 hlat.2 hsd
  have hd : Module.finrank K.E B.A = n := hF.2.2.1.trans hn
  refine GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis E w hw K e hB n B u x hF.2.2.2 (b.reindex (finCongr hd)) fun i j => ?_
  simp only [Module.Basis.reindex_apply, hb, EmbeddingLike.apply_eq_iff_eq]

end GlobalTheory.KapLat
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryModelOfSelfDualLatticeCountNeZeroStatement

section

@[expose] public section

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

theorem _root_.GlobalTheory.T.exists_unitary_model_of_selfDualLatticeCount_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  first | exact @GlobalTheory.KapLat.exists_model_of_N_ne_zero | exact GlobalTheory.KapLat.exists_model_of_N_ne_zero | (intros; apply GlobalTheory.KapLat.exists_model_of_N_ne_zero <;> assumption)
end
end
