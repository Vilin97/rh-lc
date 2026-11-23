module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleOEBasisOfIsogenousLatticeStatement
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocalPrimeGaloisActionPeriodT
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmithFactorizationEtaleOEModPrimePowStatement
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelLatticeEquivariantModPow

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

def kerMod {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) : Submodule ℤ_[l] (Fin d' → ℤ_[l]) where
  carrier := {v | ∀ i, (l : ℤ_[l]) ^ n ∣ (P *ᵥ v) i}
  add_mem' {a b} ha hb i := by
    rw [Matrix.mulVec_add]; exact dvd_add (ha i) (hb i)
  zero_mem' i := by simp
  smul_mem' c v hv i := by
    rw [Matrix.mulVec_smul]; exact Dvd.dvd.mul_left (hv i) c

theorem mulVec_mem_kerMod {d d' n : ℕ} {P : Matrix (Fin d) (Fin d') ℤ_[l]}
    {A : Matrix (Fin d') (Fin d') ℤ_[l]} {B : Matrix (Fin d) (Fin d) ℤ_[l]}
    (h : ∀ i j, (l : ℤ_[l]) ^ n ∣ (P * A - B * P) i j) {v : Fin d' → ℤ_[l]} (hv : v ∈ kerMod P n) :
    A *ᵥ v ∈ kerMod P n := by
  intro i
  have e : P *ᵥ (A *ᵥ v) = (P * A - B * P) *ᵥ v + B *ᵥ (P *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]; abel
  rw [e, Pi.add_apply]
  refine dvd_add ?_ ?_
  · show _ ∣ ∑ j, (P * A - B * P) i j * v j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (h i j) _
  · show _ ∣ ∑ j, B i j * (P *ᵥ v) j
    exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_right (hv j) _

theorem pow_ne_zero' (n : ℕ) : ((l : ℤ_[l]) ^ n) ≠ 0 :=
  pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero)

theorem finrank_kerMod {d d' n : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) :
    Module.finrank ℤ_[l] (kerMod P n) = d' := by
  apply le_antisymm
  · calc Module.finrank ℤ_[l] (kerMod P n) ≤ Module.finrank ℤ_[l] (Fin d' → ℤ_[l]) :=
          Submodule.finrank_le _
      _ = d' := by simp
  · have hm : ∀ v : Fin d' → ℤ_[l], ((l : ℤ_[l]) ^ n • LinearMap.id : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] _) v ∈ kerMod P n := by
      intro v i
      simp only [LinearMap.smul_apply, LinearMap.id_apply, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
      exact dvd_mul_right _ _
    let φ : (Fin d' → ℤ_[l]) →ₗ[ℤ_[l]] kerMod P n :=
      LinearMap.codRestrict (kerMod P n) ((l : ℤ_[l]) ^ n • LinearMap.id) hm
    have hinj : Function.Injective φ := by
      intro a b hab
      have h2 := congrArg Subtype.val hab
      simp only [φ, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h2
      exact smul_right_injective _ (pow_ne_zero' n) h2
    have := LinearMap.finrank_le_finrank_of_injective hinj
    simpa using this

end GlobalTheory.KerLat

namespace GlobalTheory.KerLat

variable {l : ℕ} [Fact l.Prime]

noncomputable def kerBasis {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Module.Basis (Fin d') ℤ_[l] (kerMod P n) :=
  Module.finBasisOfFinrankEq ℤ_[l] (kerMod P n) (finrank_kerMod P)

noncomputable def kerMat {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) :
    Matrix (Fin d') (Fin d') ℤ_[l] :=
  Matrix.of fun i j => ((kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) i

theorem kerMat_mulVec {d d' : ℕ} (P : Matrix (Fin d) (Fin d') ℤ_[l]) (n : ℕ) (w : Fin d' → ℤ_[l]) :
    kerMat P n *ᵥ w = ((∑ j, w j • kerBasis P n j : kerMod P n) : Fin d' → ℤ_[l]) := by
  ext i
  simp [kerMat, Matrix.mulVec, dotProduct, Submodule.coe_sum, Finset.sum_apply, mul_comm]

theorem exists_kernel_lattice : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  intro l _ Γ _ d d' n ρ ρ' P hP
  set b := kerBasis P n
  set f := kerMat P n
  have hf : ∀ w, f *ᵥ w = ((∑ j, w j • b j : kerMod P n) : Fin d' → ℤ_[l]) := kerMat_mulVec P n
  have hiff : ∀ v, v ∈ kerMod P n ↔ ∃ w, v = f *ᵥ w := by
    intro v; constructor
    · intro hv; refine ⟨b.repr ⟨v, hv⟩, ?_⟩
      rw [hf, b.sum_repr]
    · rintro ⟨w, rfl⟩; rw [hf]; exact Submodule.coe_mem _
  have hinj : ∀ w, f *ᵥ w = 0 → w = 0 := by
    intro w hw
    rw [hf] at hw
    have h0 : (∑ j, w j • b j) = 0 := Subtype.ext hw
    funext j
    exact Fintype.linearIndependent_iff.mp b.linearIndependent w h0 j
  have hdet : f.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    exact hw0 (hinj w hw)
  have hcancel : ∀ X Y : Matrix (Fin d') (Fin d') ℤ_[l], f * X = f * Y → X = Y := by
    intro X Y h
    have h2 := congrArg (fun M => f.adjugate * M) h
    simp only [← Matrix.mul_assoc, Matrix.adjugate_mul] at h2
    apply Matrix.ext
    intro i j
    have h3 := congrFun (congrFun h2 i) j
    simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul] at h3
    exact mul_left_cancel₀ hdet h3
  have hcol : ∀ g j, ∃ w, (ρ' g).val *ᵥ (fun i => f i j) = f *ᵥ w := by
    intro g j
    apply (hiff _).mp
    apply mulVec_mem_kerMod (A := (ρ' g).val) (B := (ρ g).val) (hP.equi g)
    exact Submodule.coe_mem (b j)
  choose W hW using hcol
  let R : Γ → Matrix (Fin d') (Fin d') ℤ_[l] := fun g => Matrix.of fun i j => W g j i
  have hR : ∀ g, f * R g = (ρ' g).val * f := by
    intro g
    apply Matrix.ext
    intro i j
    have := congrFun (hW g j) i
    simp only [Matrix.mulVec, dotProduct] at this
    simp only [Matrix.mul_apply, R, Matrix.of_apply]
    exact this.symm
  have hR1 : R 1 = 1 := hcancel _ _ (by rw [hR, map_one, Units.val_one, Matrix.one_mul, Matrix.mul_one])
  have hRm : ∀ g h, R (g * h) = R g * R h := fun g h => hcancel _ _ (by
    rw [hR, map_mul, Units.val_mul, Matrix.mul_assoc, ← hR h, ← Matrix.mul_assoc, ← hR g, Matrix.mul_assoc])
  let Rm : Γ →* Matrix (Fin d') (Fin d') ℤ_[l] := { toFun := R, map_one' := hR1, map_mul' := hRm }
  refine ⟨f, Rm.toHomUnits, hdet, fun g => hR g, fun v => hiff v⟩

end GlobalTheory.KerLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKernelLatticeEquivariantModPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_kernel_lattice_equivariant_modPow : ∀ (l : ℕ) [Fact l.Prime] (Γ : Type) [Group Γ] (d d' n : ℕ) (ρ : Γ →* GL (Fin d) ℤ_[l]) (ρ' : Γ →* GL (Fin d') ℤ_[l]) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (f : Matrix (Fin d') (Fin d') (ℤ_[l])) (ρ'' : Γ →* GL (Fin d') ℤ_[l]), f.det ≠ 0 ∧ (∀ g, f * (ρ'' g).val = (ρ' g).val * f) ∧ ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w := by
  first | exact @GlobalTheory.KerLat.exists_kernel_lattice | exact GlobalTheory.KerLat.exists_kernel_lattice | (intros; apply GlobalTheory.KerLat.exists_kernel_lattice; all_goals assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisModPow

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.BKLim.EtBasis

theorem zW_dvd {l : ℕ} [Fact l.Prime] {n : ℕ} {x : ℤ_[l]} (h : (l : ℤ_[l]) ^ n ∣ x) :
    (l : WCb l) ^ n ∣ algebraMap ℤ_[l] (WCb l) x := by
  simpa [map_pow, map_natCast] using map_dvd (algebraMap ℤ_[l] (WCb l)) h

theorem flatKer {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) (hu : ∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) : ∃ w, u = zW f *ᵥ w := by
  classical
  haveI : Module.IsTorsionFree ℤ_[l] (WCb l) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact (WittVector.map_injective _ (ZMod.castHom_injective (Cb l))).comp (WittVector.equiv l).symm.injective
  choose y hy using hu
  let x : ((Fin d' ⊕ Fin d) → ℤ_[l]) →ₗ[ℤ_[l]] WCb l := Fintype.linearCombination ℤ_[l] (Sum.elim u y)
  let B : Matrix (Fin d' ⊕ Fin d) (Fin d) ℤ_[l] :=
    Matrix.fromRows Piᵀ (Matrix.diagonal fun _ => -((l : ℤ_[l]) ^ n))
  let F : (Fin d → ℤ_[l]) →ₗ[ℤ_[l]] ((Fin d' ⊕ Fin d) → ℤ_[l]) := Matrix.toLin' B
  have hxF : x ∘ₗ F = 0 := by
    ext i : 2
    have := hy i
    simp [x, F, B, Fintype.linearCombination_apply, Fintype.sum_sum_type, Matrix.mulVec, dotProduct,
      Algebra.smul_def, Matrix.diagonal_apply] at this ⊢
    rw [this]
    simp [apply_ite (algebraMap ℤ_[l] (WCb l)), ite_mul]
  obtain ⟨k, a, yy, hx, haF⟩ := Module.Flat.exists_factorization_of_comp_eq_zero_of_free hxF
  let A : Fin k → (Fin d' ⊕ Fin d) → ℤ_[l] := fun m p => a (fun q => if p = q then 1 else 0) m
  have hyy : ∀ v : Fin k →₀ ℤ_[l], yy v = ∑ m, v m • yy (Finsupp.single m 1) := by
    intro v
    have : yy = Finsupp.linearCombination ℤ_[l] (fun m => yy (Finsupp.single m 1)) := by
      refine Finsupp.lhom_ext fun m r => ?_
      rw [Finsupp.linearCombination_single, ← map_smul, Finsupp.smul_single_one]
    conv_lhs => rw [this]
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
    simp
  have hA : ∀ m i, (Pi *ᵥ fun j => A m (Sum.inl j)) i = (l : ℤ_[l]) ^ n * A m (Sum.inr i) := by
    intro m i
    have h0 := congrArg (fun v => v m) (LinearMap.congr_fun haF (_root_.Pi.single i 1))
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, Finsupp.coe_zero, _root_.Pi.zero_apply] at h0
    rw [LinearMap.pi_apply_eq_sum_univ] at h0
    simp [A, F, B, Fintype.sum_sum_type, Matrix.mulVec, dotProduct, Matrix.diagonal_apply, _root_.Pi.single_apply] at h0 ⊢
    linear_combination h0
  have hu' : ∀ j, u j = ∑ m, A m (Sum.inl j) • yy (Finsupp.single m 1) := by
    intro j
    have h1 : u j = x (fun q => if Sum.inl j = q then 1 else 0) := by
      simp [x, Fintype.linearCombination_apply, Fintype.sum_sum_type]
    rw [h1, hx, LinearMap.comp_apply, hyy]
  choose w hw using fun m => (hker (fun j => A m (Sum.inl j))).1 (fun i => ⟨A m (Sum.inr i), hA m i⟩)
  refine ⟨fun t => ∑ m, w m t • yy (Finsupp.single m 1), funext fun j => ?_⟩
  rw [hu' j]
  have h2 : ∀ m, A m (Sum.inl j) = ∑ t, f j t * w m t := fun m => congrFun (hw m) j

  simp only [h2, Matrix.mulVec, dotProduct, Finset.sum_smul, Finset.mul_sum, Finset.sum_mul, Algebra.smul_def, Matrix.map_apply,
  map_sum, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem kerW {l : ℕ} [Fact l.Prime] {d d' n : ℕ} (Pi : Matrix (Fin d) (Fin d') ℤ_[l])
    (f : Matrix (Fin d') (Fin d') ℤ_[l])
    (hker : ∀ v : Fin d' → ℤ_[l], (∀ i, (l : ℤ_[l]) ^ n ∣ (Pi *ᵥ v) i) ↔ ∃ w, v = f *ᵥ w)
    (u : Fin d' → WCb l) : (∀ i, (l : WCb l) ^ n ∣ (zW Pi *ᵥ u) i) ↔ ∃ w, u = zW f *ᵥ w := by
  refine ⟨flatKer Pi f hker u, ?_⟩
  rintro ⟨w, rfl⟩ i
  have hPf : ∀ i j, (l : ℤ_[l]) ^ n ∣ (Pi * f) i j := by
    intro i j
    have := (hker (f *ᵥ _root_.Pi.single j 1)).2 ⟨_, rfl⟩ i
    rw [Matrix.mul_apply]
    simpa [Matrix.mulVec, dotProduct, _root_.Pi.single_apply] using this
  have hm : zW Pi * zW f = zW (Pi * f) := (Matrix.map_mul).symm
  rw [Matrix.mulVec_mulVec, hm]
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (zW_dvd (hPf i j)) _

end GlobalTheory.BKLim.EtBasis


open GlobalTheory.BKLim.EtBasis in
theorem GlobalTheory.BKLim.etBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  intro l _ K bk τ hτ N d d' n ρ ρ' F' Pi hn hOnto
  obtain ⟨f, ρ'', hdet, hfeq, hker⟩ := GlobalTheory.T.exists_kernel_lattice_equivariant_modPow l (↥(GK K)) d d' n ρ ρ' Pi hOnto
  obtain ⟨T'', P, hT'', hP, hfT⟩ := GlobalTheory.T.exists_etale_OE_basis_of_isogenous_lattice l K bk τ hτ N d' (fun g => (ρ' g).val)
    (fun g => (ρ'' g).val) F' f hdet (fun g => (ρ'' g).isUnit) hfeq
  have hTd := (Matrix.isUnit_iff_isUnit_det _).1 F'.unit
  have hT''d := (Matrix.isUnit_iff_isUnit_det _).1 hT''
  apply GlobalTheory.T.exists_smith_factorization_etale_OE_mod_prime_pow l K bk d d' n (zW Pi * F'.T) P hn hP
  · obtain ⟨S, hS⟩ := hOnto.surj
    refine ⟨F'.T⁻¹ * zW S, fun i j => ?_⟩
    have : zW Pi * F'.T * (F'.T⁻¹ * zW S) - 1 = zW (Pi * S - 1) := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc F'.T, Matrix.mul_nonsing_inv _ hTd, Matrix.one_mul]
      show _ = (algebraMap ℤ_[l] (WCb l)).mapMatrix (Pi * S - 1)
      rw [map_sub, map_one, RingHom.mapMatrix_apply, Matrix.map_mul]
    rw [this]
    exact zW_dvd (hS i j)
  · intro v
    rw [← Matrix.mulVec_mulVec, kerW Pi f hker]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨T''⁻¹ *ᵥ w, ?_⟩
      have h1 : zW f = F'.T * P * T''⁻¹ := by
        rw [← hfT, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hT''d, Matrix.mul_one]
      calc v = F'.T⁻¹ *ᵥ (F'.T *ᵥ v) := by
            rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mulVec]
        _ = P *ᵥ (T''⁻¹ *ᵥ w) := by
            rw [hw, h1]
            simp only [Matrix.mulVec_mulVec]
            rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hTd, Matrix.one_mul]
    · rintro ⟨w, rfl⟩
      exact ⟨T'' *ᵥ w, by simp only [Matrix.mulVec_mulVec, hfT]⟩
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEtaleBasisModPowStatement

section

@[expose] public section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

theorem _root_.GlobalTheory.T.exists_etaleBasis_modPow : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (N d d' n : ℕ) (ρ : ↥(GK K) →* GL (Fin d) ℤ_[l]) (ρ' : ↥(GK K) →* GL (Fin d') ℤ_[l]) (F' : Pre bk N d' fun g => (ρ' g).val) (Pi : Matrix (Fin d) (Fin d') (ℤ_[l])), 1 ≤ n → Onto (fun g => (ρ g).val) (fun g => (ρ' g).val) Pi n → ∃ (Tn : Matrix (Fin d) (Fin d) (WCb l)) (R : Matrix (Fin d) (Fin d') (WCb l)) (R' : Matrix (Fin d') (Fin d) (WCb l)), IsUnit Tn ∧ (∀ i j, R i j ∈ bk.OE) ∧ (∀ i j, R' i j ∈ bk.OE) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T - Tn * R) i j) ∧ (∀ i j, (l : WCb l) ^ n ∣ (zW Pi * F'.T * R' - Tn) i j) := by
  first | exact @GlobalTheory.BKLim.etBasis_modPow | exact GlobalTheory.BKLim.etBasis_modPow | (intros; apply GlobalTheory.BKLim.etBasis_modPow <;> assumption)
end
end
