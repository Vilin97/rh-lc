module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.PairHermSmulRight
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
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.RelIndexSmulSub
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.ProdEta
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.EventuallySmulSub
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.BHRSmulRight
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.MemUnifOIff
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfBas

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.HermitianBasisBelowSecond

section

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

def hd {a : ℕ} (i : Fin a) : HermR (Fv F v) σ a :=
  ⟨Matrix.single i i 1, fun p q => by
    rw [Matrix.single_apply, Matrix.single_apply, apply_ite (sigR (Fv F v) σ), map_one, map_zero]
    exact if_congr and_comm rfl rfl⟩

theorem hm_apply_ne {a : ℕ} (hinv : ∀ y, σ (σ y) = y) {k l i j : Fin a} (c : Fv F v ⊗[F] E)
    (h1 : ¬(k = i ∧ l = j)) (h2 : ¬(l = i ∧ k = j)) :
    (hm σ v hinv k l c : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show (Matrix.single k l c + Matrix.single l k (sigR (Fv F v) σ c)) i j = 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg h1, if_neg h2, add_zero]

theorem hd_apply_ne {a : ℕ} {k i j : Fin a} (h : ¬(k = i ∧ k = j)) :
    (hd σ v k : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  show Matrix.single k k (1 : Fv F v ⊗[F] E) i j = 0
  rw [Matrix.single_apply, if_neg h]

def hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (p : Fin a × Fin a) : HermR (Fv F v) σ a :=
  if p.1 < p.2 then hm σ v hinv p.1 p.2 (β 0) else if p.2 < p.1 then hm σ v hinv p.2 p.1 (β 1) else hd σ v p.1

theorem hb_zero {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {p : Fin a × Fin a} {i j : Fin a}
    (hp1 : p ≠ (i, j)) (hp2 : p ≠ (j, i)) : (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
  obtain ⟨k, l⟩ := p
  unfold hb
  dsimp only
  split_ifs with hkl hlk
  · exact hm_apply_ne σ v hinv _ (fun e => hp1 (Prod.ext e.1 e.2)) (fun e => hp2 (Prod.ext e.2 e.1))
  · exact hm_apply_ne σ v hinv _ (fun e => hp2 (Prod.ext e.2 e.1)) (fun e => hp1 (Prod.ext e.1 e.2))
  · have hkl' : k = l := le_antisymm (not_lt.1 hlk) (not_lt.1 hkl)
    subst hkl'
    exact hd_apply_ne σ v (fun e => hp1 (Prod.ext e.1 e.2))

theorem hermitian_basis_above_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 0 := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single i j (β 0) + Matrix.single j i (sigR (Fv F v) σ (β 0))) i j = β 0
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_above_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : i < j) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = β 1 := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single i j (β 1) + Matrix.single j i (sigR (Fv F v) σ (β 1))) i j = β 1
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_pos ⟨rfl, rfl⟩,
    if_neg (fun e => h.ne e.2), add_zero]

theorem hermitian_basis_below_first {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (i, j) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 1) := by
  unfold hb
  rw [if_neg (not_lt.2 h.le), if_pos h]
  show (Matrix.single j i (β 1) + Matrix.single i j (sigR (Fv F v) σ (β 1))) i j = sigR (Fv F v) σ (β 1)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hermitian_basis_below_second {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) {i j : Fin a} (h : j < i) :
    (hb σ v hinv β (j, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = sigR (Fv F v) σ (β 0) := by
  unfold hb
  rw [if_pos h]
  show (Matrix.single j i (β 0) + Matrix.single i j (sigR (Fv F v) σ (β 0))) i j = sigR (Fv F v) σ (β 0)
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply, if_neg (fun e => h.ne e.1),
    if_pos ⟨rfl, rfl⟩, zero_add]

theorem hb_eq {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (i : Fin a) :
    (hb σ v hinv β (i, i) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i = 1 := by
  unfold hb
  rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  show Matrix.single i i (1 : Fv F v ⊗[F] E) i i = 1
  rw [Matrix.single_apply, if_pos ⟨rfl, rfl⟩]

theorem coe_sum_hb {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i j : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      ∑ p, c p • (hb σ v hinv β p : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := by
  rw [AddSubmonoidClass.coe_finsetSum, Matrix.sum_apply]
  rfl

theorem sum_lt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : i < j) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • β 0 + c (j, i) • β 1 := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_above_first σ v hinv β h, hermitian_basis_above_second σ v hinv β h]

theorem sum_gt {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    {i j : Fin a} (h : j < i) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j =
      c (i, j) • sigR (Fv F v) σ (β 1) + c (j, i) • sigR (Fv F v) σ (β 0) := by
  have hne : ((i, j) : Fin a × Fin a) ≠ (j, i) := fun e => h.ne' (Prod.ext_iff.1 e).1
  rw [coe_sum_hb, Fintype.sum_eq_add (i, j) (j, i) hne
    (fun p hp => by rw [hb_zero σ v hinv β hp.1 hp.2, smul_zero]), hermitian_basis_below_first σ v hinv β h, hermitian_basis_below_second σ v hinv β h]

theorem sum_diag {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (c : Fin a × Fin a → Fv F v)
    (i : Fin a) :
    ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i i =
      sc (E := E) v (c (i, i)) := by
  rw [coe_sum_hb, Fintype.sum_eq_single (i, i) (fun p hp => by rw [hb_zero σ v hinv β hp hp, smul_zero]),
    hb_eq, sc, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

end PI.OmLocU.SdB
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.OEvBasis

section

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

theorem genIdx {W : Type} [AddCommGroup W] [Module (Fv F v) W] {ι : Type} [Fintype ι] (M : AddSubgroup W)
    (b : ι → W) (hb : LinearIndependent (Fv F v) b)
    (hmem : ∀ x, x ∈ M ↔ ∃ c : ι → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • b i)
    (ϖ : Fv F v) (hϖ : IsUnif v ϖ) :
    (smulSub ϖ M).relIndex M = (Ideal.absNorm v.asIdeal) ^ (Fintype.card ι) := by
  classical
  let φ : (ι → v.adicCompletionIntegers F) →+ M :=
    { toFun := fun c => ⟨∑ i, (c i : Fv F v) • b i, (hmem _).2 ⟨c, rfl⟩⟩
      map_zero' := by ext1; simp
      map_add' := fun c d => by
        ext1
        simp [add_smul, Finset.sum_add_distrib] }
  have hφs : Function.Surjective φ := by
    rintro ⟨x, hx⟩
    obtain ⟨c, rfl⟩ := (hmem x).1 hx
    exact ⟨c, rfl⟩
  have hsm : ∀ d : ι → v.adicCompletionIntegers F,
      ϖ • ∑ i, (d i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
    intro d
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => smul_smul _ _ _
  have key : ((smulSub ϖ M).addSubgroupOf M).comap φ =
      AddSubgroup.pi Set.univ (fun _ => unifO v ϖ) := by
    ext c
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
    constructor
    · intro hc i _
      obtain ⟨z, hz, hze⟩ := (mem_smulSub ϖ M _).1 hc
      obtain ⟨d, rfl⟩ := (hmem z).1 hz
      refine ⟨d i, ?_⟩
      have e : ∑ i, (c i : Fv F v) • b i = ∑ i, (ϖ * d i) • b i := by
        rw [← hsm, hze]
        rfl
      have h0 := Fintype.linearIndependent_iff.1 hb (fun i => (c i : Fv F v) - ϖ * d i)
        (by simp only [sub_smul, Finset.sum_sub_distrib, e, sub_self])
      exact sub_eq_zero.1 (h0 i)
    · intro h
      choose d hd using fun i => h i (Set.mem_univ i)
      refine (mem_smulSub ϖ M _).2 ⟨∑ i, (d i : Fv F v) • b i, (hmem _).2 ⟨d, rfl⟩, ?_⟩
      rw [hsm]
      show ∑ i, (ϖ * d i) • b i = ∑ i, (c i : Fv F v) • b i
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hd i]
  rw [AddSubgroup.relIndex, ← AddSubgroup.index_comap_of_surjective _ hφs, key, AddSubgroup.index_pi]
  simp only [resIdx_holds v ϖ hϖ, Finset.prod_const, Finset.card_univ]

theorem oEv_basis : ∃ β : Fin (Module.finrank F E) → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin (Module.finrank F E) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • β i := by
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  set M := Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) with hM
  have : Module.Finite (v.adicCompletionIntegers F) M := Module.Finite.iff_fg.2 (b_fg v)
  have : Module.IsTorsionFree (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
    Module.IsTorsionFree.of_smul_eq_zero fun r x h => by
      have h' : (r : Fv F v) • x = 0 := h
      rcases smul_eq_zero.1 h' with h0 | h0
      · exact Or.inl (Subtype.ext h0)
      · exact Or.inr h0
  have : Module.Free (v.adicCompletionIntegers F) M := Module.free_of_finite_type_torsion_free'
  let bM := Module.finBasis (v.adicCompletionIntegers F) M
  let b0 : Fin (Module.finrank (v.adicCompletionIntegers F) M) → Fv F v ⊗[F] E := fun i => (bM i : _)
  have hli0 : LinearIndependent (v.adicCompletionIntegers F) b0 :=
    bM.linearIndependent.map' M.subtype (Submodule.ker_subtype M)
  have hli : LinearIndependent (Fv F v) b0 :=
    (LinearIndependent.iff_fractionRing (v.adicCompletionIntegers F) (Fv F v)).1 hli0
  have hmem : ∀ x, x ∈ M ↔ ∃ c : Fin (Module.finrank (v.adicCompletionIntegers F) M) → v.adicCompletionIntegers F,
      x = ∑ i, (c i : Fv F v) • b0 i := by
    intro x
    constructor
    · intro hx
      refine ⟨fun i => bM.repr ⟨x, hx⟩ i, ?_⟩
      have h := congrArg Subtype.val (bM.sum_repr ⟨x, hx⟩)
      rw [Submodule.coe_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun i _ => rfl)
    · rintro ⟨c, rfl⟩
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem M (c i) (bM i).2
  have hsp : ⊤ ≤ Submodule.span (Fv F v) (Set.range b0) := by
    have hM0 : ∀ x ∈ M, x ∈ Submodule.span (Fv F v) (Set.range b0) := by
      intro x hx
      obtain ⟨c, rfl⟩ := (hmem x).1 hx
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    intro x _
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c e =>
      have hal : IsAlgebraic ℤ e := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ e)
      obtain ⟨m, hm0, hI⟩ := hal.exists_integral_multiple
      have hmF : (m : Fv F v) ≠ 0 := by
        rw [← map_intCast (algebraMap F (Fv F v))]
        exact (map_ne_zero _).2 (Int.cast_ne_zero.2 hm0)
      have e2 : inclR (F := F) (Fv F v) (m • e) = (m : Fv F v) • inclR (F := F) (Fv F v) e := by
        rw [map_zsmul, Int.cast_smul_eq_zsmul]
      have e3 : c ⊗ₜ[F] e = c • inclR (F := F) (Fv F v) e := by
        simp [inclR, TensorProduct.smul_tmul']
      have e1 : c ⊗ₜ[F] e = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) ((⟨m • e, hI⟩ : 𝓞 E) : E) := by
        show _ = (c * (m : Fv F v)⁻¹) • inclR (F := F) (Fv F v) (m • e)
        rw [e2, smul_smul, mul_assoc, inv_mul_cancel₀ hmF, mul_one, e3]
      rw [e1]
      exact Submodule.smul_mem _ _ (hM0 _ (b_inclR_mem (F := F) (E := E) v ⟨m • e, hI⟩))
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hrk : Module.finrank (v.adicCompletionIntegers F) M = Module.finrank F E := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp)
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_baseChange]
  refine ⟨fun i => b0 (Fin.cast hrk.symm i), ?_, fun x => ?_⟩
  · exact hli.comp _ (Fin.cast_injective _)
  · rw [show x ∈ OEv (E := E) v ↔ x ∈ M from Iff.rfl, hmem]
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk.symm i), ?_⟩
      exact (Fintype.sum_equiv (finCongr hrk) _ _ (fun i => rfl))
    · rintro ⟨c, rfl⟩
      refine ⟨fun i => c (Fin.cast hrk i), ?_⟩
      exact Fintype.sum_equiv (finCongr hrk.symm) _ _ (fun i => by simp)

end PI.OmLocU.SdB
end
end
end

-- Source module: Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.SigRSmulF

section

@[expose] public section

noncomputable section

namespace PI.OmLocU.SdB

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain PI.OmLocU PI.VolStabSW
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F))

theorem oEv_basis2 (hfin : Module.finrank F E = 2) : ∃ β : Fin 2 → Fv F v ⊗[F] E, LinearIndependent (Fv F v) β ∧
    ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i := by
  have h := oEv_basis (E := E) v
  rw [hfin] at h
  exact h

theorem sigR_smulF (c : Fv F v) (x : Fv F v ⊗[F] E) : sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul a b => simp [sigR, TensorProduct.smul_tmul']
  | add x y hx hy => rw [smul_add, map_add (f := _), map_add (f := _), hx, hy, smul_add]

theorem hb_li {a : ℕ} (hinv : ∀ y, σ (σ y) = y) (β : Fin 2 → Fv F v ⊗[F] E) (hβ : LinearIndependent (Fv F v) β) :
    LinearIndependent (Fv F v) (hb σ v hinv β (a := a)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc p
  have hent : ∀ i j, ((∑ p, c p • hb σ v hinv β p : HermR (Fv F v) σ a) :
      Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j = 0 := by
    intro i j
    rw [hc]
    rfl
  have hβ2 := Fintype.linearIndependent_iff.1 hβ
  obtain ⟨i, j⟩ := p
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 := hent i j
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (i, j), c (j, i)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 0
  · have h1 := hent i i
    rw [sum_diag σ v hinv β c i, b_sc_eq] at h1
    exact (map_eq_zero_iff _ (algebraMap (Fv F v) (Fv F v ⊗[F] E)).injective).1 h1
  · have h1 := hent j i
    rw [sum_lt σ v hinv β c h] at h1
    have h0 := hβ2 ![c (j, i), c (i, j)] (by simpa [Fin.sum_univ_two] using h1)
    simpa using h0 1

theorem fix_int' (hcm : IsCMExt F E σ) {t : Fv F v ⊗[F] E} (ht : t ∈ OEv (E := E) v)
    (hf : sigR (Fv F v) σ t = t) : ∃ r ∈ v.adicCompletionIntegers F, t = sc (E := E) v r := by
  have hinv := b_sig_sig σ hcm
  have hnt := b_sig_nt σ hcm
  have hfin := hcm.2.2.1
  set r : Fv F v := algebraMap F (Fv F v) (1 / 2) * Algebra.trace (Fv F v) (Fv F v ⊗[F] E) t with hr
  have hsc : sc (E := E) v r = t := by
    calc sc (E := E) v r
        = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2)) * (t + t) := by
          rw [b_sc_eq, hr, map_mul, trace_v v σ hinv hnt hfin, hf]
      _ = algebraMap (Fv F v) (Fv F v ⊗[F] E) (algebraMap F (Fv F v) (1 / 2) * 2) * t := by
          rw [map_mul, map_ofNat, mul_assoc, two_mul]
      _ = t := by rw [half_two, map_one, one_mul]
  refine ⟨r, b_int_of_sc v (hsc ▸ ht), hsc.symm⟩

theorem hb_mem {a : ℕ} (hcm : IsCMExt F E σ) (β : Fin 2 → Fv F v ⊗[F] E)
    (hβ : ∀ x, x ∈ OEv (E := E) v ↔ ∃ c : Fin 2 → v.adicCompletionIntegers F, x = ∑ i, (c i : Fv F v) • β i)
    (T : HermR (Fv F v) σ a) :
    T ∈ HO σ v a ↔ ∃ c : Fin a × Fin a → v.adicCompletionIntegers F,
      T = ∑ p, (c p : Fv F v) • hb σ v (b_sig_sig σ hcm) β p := by
  have hinv := b_sig_sig σ hcm
  constructor
  · intro hT
    have hT' : ∀ i j, (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := hT
    have hH : ∀ i j, sigR (Fv F v) σ ((T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) j i) =
        (T : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j := fun i j => T.2 i j
    choose d hd using fun i j => (hβ _).1 (hT' i j)
    choose r hr hrT using fun i => fix_int' σ v hcm (hT' i i) (hH i i)
    refine ⟨fun p => if p.1 < p.2 then d p.1 p.2 0 else if p.2 < p.1 then d p.2 p.1 1 else ⟨r p.1, hr p.1⟩, ?_⟩
    apply Subtype.ext
    ext i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h, hd i j, Fin.sum_univ_two]
      simp [h, not_lt.2 h.le]
    · rw [sum_diag σ v hinv β _ i, hrT i]
      simp
    · rw [sum_gt σ v hinv β _ h, ← hH i j, hd j i, Fin.sum_univ_two, map_add (f := _), sigR_smulF, sigR_smulF, add_comm]
      simp [h, not_lt.2 h.le]
  · rintro ⟨c, rfl⟩
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · rw [sum_lt σ v hinv β _ h]
      exact (hβ _).2 ⟨![c (i, j), c (j, i)], by simp [Fin.sum_univ_two]⟩
    · rw [sum_diag σ v hinv β _ i]
      exact b_sc_mem v (c (i, i)).2
    · rw [sum_gt σ v hinv β _ h]
      have hm := b_sigR_mem v σ ((hβ ((c (j, i) : Fv F v) • β 0 + (c (i, j) : Fv F v) • β 1)).2
        ⟨![c (j, i), c (i, j)], by simp [Fin.sum_univ_two]⟩)
      rwa [map_add, sigR_smulF, sigR_smulF, add_comm] at hm

theorem idxPiH_std (a : ℕ) (hS : StdHyp σ J ψ) : IdxPiH σ v a := by
  intro _ ϖ hϖ
  have hcm := hS.1
  obtain ⟨β, hli, hβ⟩ := oEv_basis2 v hcm.2.2.1
  rw [genIdx v (HO σ v a) (hb σ v (b_sig_sig σ hcm) β) (hb_li σ v (b_sig_sig σ hcm) β hli)
    (hb_mem σ v hcm β hβ) ϖ hϖ, qv, Fintype.card_prod, Fintype.card_fin]
  push_cast
  ring

end PI.OmLocU.SdB
end
end
end
