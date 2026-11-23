module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWE
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixThA
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWA
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
import Mathlib.Tactic.Polynomial.Basic
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.UnitTriv
import Mathlib.Tactic.Basify
import Std.Tactic.BVDecide.Normalize.Prop

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWF

section

@[expose] public section

noncomputable section




open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

def UnitTriv (D : D7) (χ : (AE D)ˣ →* Circle) (S : Finset (Pl D)) : Prop :=
  ∀ u : (AE D)ˣ, (∀ w, compInf D.host.F D.host.E w (u : AE D) = 1) → (∀ v ∈ S, cv D v (u : AE D) = 1) →
    (∀ v ∉ S, cv D v (u : AE D) ∈ intLoc D.host.F D.host.E v ∧
      cv D v ((u⁻¹ : (AE D)ˣ) : AE D) ∈ intLoc D.host.F D.host.E v) → χ u = 1 ∧ absA D u = 1

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  have := congrFun (congrFun (adj_adj (D := D) (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => z)) 0) 0
  simpa [adj] using this

theorem det_mem_intLoc {v : Pl D} {M : Matrix (Fin n) (Fin n) (Fv D.host.F v ⊗[D.host.F] D.host.E)}
    (h : ∀ i j, M i j ∈ intLoc D.host.F D.host.E v) : M.det ∈ intLoc D.host.F D.host.E v := by
  let M' : Matrix (Fin n) (Fin n) (intLoc D.host.F D.host.E v) := fun i j => ⟨M i j, h i j⟩
  have h1 := (intLoc D.host.F D.host.E v).subtype.map_det M'
  have e : (intLoc D.host.F D.host.E v).subtype.mapMatrix M' = M := by ext i j; rfl
  rw [e] at h1
  rw [← h1]
  exact (M'.det).2

theorem map_one_entry {R : Type} [CommRing R] (f : AE D →+* R) (k j : Fin n) :
    f ((1 : Mx D n n) k j) = (1 : Matrix (Fin n) (Fin n) R) k j := by
  by_cases h : k = j
  · subst h; simp
  · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]

variable {S : Finset (Pl D)} {e : AE D}

theorem fixM (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
    {μ : Measure (Mx D V.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)} (hω : IsWeilSch ψ χ θ V μ ω)
    (he : IsIdem S e) (hU : UnitTriv D χ S) {g : G D n} (hg : g ∈ KOff D n S) (hM : IsM g)
    (Ψ : schwartzA θ V.rank n) (hΨ : Good S e Ψ.1) : ω g Ψ = Ψ := by
  obtain ⟨a, ha⟩ := hM
  have hll : ∀ i j, a.1 i j = mat g (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) := fun i j => by
    rw [ha, block_matrix_apply_inl_inl_alt]
  have hrr : ∀ i j, (a⁻¹).1 i j = cA D (mat g (finSumFinEquiv (Sum.inr j)) (finSumFinEquiv (Sum.inr i))) := fun i j => by
    rw [ha, block_matrix_apply_inr_inr_alt]
    show _ = cA D (cA D ((a⁻¹).1 i j))
    rw [cA_cA]
  have hinf : ∀ w i j, compInf D.host.F D.host.E w (a.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := fun w i j => by
    rw [hll, LFixTh.kOff_inf hg, one_ll]
  have hat : ∀ v ∈ S, ∀ i j, cv D v (a.1 i j) = (1 : Matrix (Fin n) (Fin n) _) i j := fun v hv i j => by
    rw [hll, LFixTh.kOff_at hg hv, one_ll]
  have hint : ∀ i j, IntS S (a.1 i j) := fun i j v hv => by rw [hll]; exact (LFixTh.kOff_int hg hv _ _).1
  have hint' : ∀ i j, IntS S ((a⁻¹).1 i j) := fun i j => by
    rw [hrr]
    exact IntS.cA (fun v hv => (LFixTh.kOff_int hg hv _ _).1)
  have hone : ∀ k j, IntS S ((1 : Mx D n n) k j) := fun k j v _ => by
    rw [map_one_entry]
    by_cases h : k = j
    · subst h; rw [Matrix.one_apply_eq]; exact one_mem _
    · rw [Matrix.one_apply_ne h]; exact zero_mem _
  have hoff : ∀ k j, OffS S (a.1 k j - (1 : Mx D n n) k j) := fun k j =>
    ⟨fun w => by rw [RingHom.map_sub, hinf, map_one_entry, sub_self],
      fun v hv => by rw [RingHom.map_sub, hat v hv, map_one_entry, sub_self],
      (hint k j).add (hone k j).neg⟩
  set u := Matrix.GeneralLinearGroup.det a with hudef
  have hu : (u : AE D) = a.1.det := Matrix.GeneralLinearGroup.val_det_apply a
  have hu' : ((u⁻¹ : (AE D)ˣ) : AE D) = (a⁻¹).1.det := by
    rw [hudef, ← map_inv]; exact Matrix.GeneralLinearGroup.val_det_apply _
  have hmap : ∀ {R : Type} [CommRing R] (f : AE D →+* R), (∀ i j, f (a.1 i j) = (1 : Matrix (Fin n) (Fin n) R) i j) →
      f a.1.det = 1 := by
    intro R _ f hf
    rw [RingHom.map_det]
    have : f.mapMatrix a.1 = 1 := by ext i j; exact hf i j
    rw [this, Matrix.det_one]
  obtain ⟨hχu, habs⟩ := hU u (fun w => by rw [hu]; exact hmap _ (hinf w)) (fun v hv => by rw [hu]; exact hmap _ (hat v hv))
    (fun v hv => ⟨by rw [hu, RingHom.map_det]; exact det_mem_intLoc fun i j => hint i j v hv,
      by rw [hu', RingHom.map_det]; exact det_mem_intLoc fun i j => hint' i j v hv⟩)
  have hxa : ∀ x : Mx D V.rank n, IntOff S (x * a.1) ↔ IntOff S x := by
    intro x
    rw [intOff_iff, intOff_iff]
    constructor
    · intro h i j
      have ex : x = (x * a.1) * (a⁻¹).1 := by
        rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
      rw [ex]
      exact intS_mul h hint' i j
    · intro h i j
      exact intS_mul h hint i j
  have hexa : ∀ x : Mx D V.rank n, e • (x * a.1) = e • x := by
    intro x
    ext i j
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum]
    have : ∀ k, e * (x i k * a.1 k j) = e * (x i k * (1 : Mx D n n) k j) := by
      intro k
      have h0 := idem_mul_offS he (hoff k j)
      linear_combination (x i k) * h0
    simp_rw [this, ← Finset.mul_sum, ← Matrix.mul_apply, Matrix.mul_one]
  refine Subtype.ext (funext fun x => ?_)
  rw [hω.levi g a ha Ψ x]
  change (χ u : ℂ) * npow (absA D u) ((V.rank : ℂ) / 2) * Ψ.1 (x * a.1) = Ψ.1 x
  rw [hχu, habs]
  simp only [npow, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, Circle.coe_one, one_mul]
  rw [hΨ (x * a.1), hΨ x, hxa, hexa]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LFixWG

section

@[expose] public section

noncomputable section




open scoped Matrix NNReal TensorProduct
open IsDedekindDomain NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.AdelicU
  GlobalTheory.MixModel GlobalTheory.StdUnn GlobalTheory.Doubling Filter MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Rsw.L.LFixW

variable {D : D7} {n : ℕ}

theorem adj_neg_one : adj (-1 : Mx D n n) = -1 := by
  rw [adj_neg]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h; simp [adj]
  · simp [adj, Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]

theorem intOff_neg {S : Finset (Pl D)} {a b : ℕ} (x : Mx D a b) : IntOff S (-x) ↔ IntOff S x := by
  rw [intOff_iff, intOff_iff]
  refine ⟨fun h i j => ?_, fun h i j => (h i j).neg⟩
  have := (h i j).neg
  rwa [Matrix.neg_apply, neg_neg] at this

theorem absA_ne (u : (AE D)ˣ) : absA D u ≠ 0 := by
  intro h0
  have := map_mul (absA D) u u⁻¹
  rw [mul_inv_cancel, map_one, h0, zero_mul] at this
  exact zero_ne_one this.symm

theorem npow_ne (r : ℝ≥0) (hr : r ≠ 0) (t : ℂ) : npow r t ≠ 0 := by
  intro h
  have := (Complex.cpow_eq_zero_iff _ _).1 h
  exact hr (by exact_mod_cast this.1)

theorem fixWc (V : HSp D) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) :
    ∃ S₀ : Finset (Pl D), ∀ S, S₀ ⊆ S → ∀ e, IsIdem S e → ∀ (n : ℕ) (θ : InfFam D) (μ : Measure (Mx D V.rank n))
      (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (χ : (AE D)ˣ →* Circle), IsWeilSch ψ χ θ V μ ω →
      μ.IsAddHaarMeasure → ∀ w u : G D n, IsW w → IsN u → u ∈ KOff D n S → ∀ Φ : schwartzA θ V.rank n,
        Good S e Φ.1 → ω (w * u * w⁻¹) Φ = Φ := by
  classical
  obtain ⟨S₁, hS₁⟩ := fixN V hψ
  obtain ⟨S₂, hS₂⟩ := ft_supp V.gram (gram_det_ne V) hψ
  refine ⟨S₁ ∪ S₂, fun S hS e he n θ μ ω χ hω hμ w u hw hNu hu Φ hΦ => ?_⟩
  set Φ' := ω (w⁻¹ * w⁻¹) Φ with hΦ'
  have hmw : mat (w * w) = blk4 ((-1 : GL (Fin n) (AE D)) : Mx D n n) 0 0
      (adj (((-1 : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Mx D n n)) := by
    rw [LFixTh.mat_mul, hw, block_matrix_mul_comm_ring, inv_neg, inv_one, Units.val_neg, Units.val_one, adj_neg_one]
    simp
  set c : ℂ := (χ (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D))) : ℂ) *
    npow (absA D (Matrix.GeneralLinearGroup.det (-1 : GL (Fin n) (AE D)))) ((V.rank : ℂ) / 2) with hcdef
  have hc0 : c ≠ 0 := mul_ne_zero (Circle.coe_ne_zero _) (npow_ne _ (absA_ne _) _)
  have hww : ω (w * w) Φ' = Φ := by
    rw [hΦ', ← Module.End.mul_apply, ← map_mul]
    have : w * w * (w⁻¹ * w⁻¹) = 1 := by group
    rw [this, map_one, Module.End.one_apply]
  have hc : ∀ y, Φ.1 y = c * Φ'.1 (-y) := by
    intro y
    have h := hω.levi (w * w) (-1) hmw Φ' y
    rw [hww] at h
    rw [h, Units.val_neg, Units.val_one, Matrix.mul_neg, Matrix.mul_one]
  have hc' : ∀ y, Φ'.1 y = c⁻¹ * Φ.1 (-y) := by
    intro y
    rw [hc (-y), neg_neg, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]
  have hgood : Good S e Φ'.1 := by
    refine good_of he (fun y hy => ?_) (fun y z hz => ?_)
    · rw [hc', good_supp hΦ (fun h => hy ((intOff_neg y).1 h)), mul_zero]
    · rw [hc', hc', neg_add, good_shift he hΦ (-y) (z := -z) (fun i j => (hz i j).neg)]
  have hsupp : ∀ x, ¬ IntOff S x → (ω w⁻¹ Φ).1 x = 0 := by
    intro x hx
    have e1 : ω w⁻¹ Φ = ω w Φ' := by
      rw [hΦ', ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    rw [e1, hω.weyl w hw Φ' x]
    exact hS₂ S (fun v h => hS (Finset.mem_union_right _ h)) e he n μ hμ Φ'.1 hgood x hx
  have hfix := hS₁ S (fun v h => hS (Finset.mem_union_left _ h)) n θ μ ω χ hω u hu hNu (ω w⁻¹ Φ) hsupp
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix, ← Module.End.mul_apply, ← map_mul,
    mul_inv_cancel, map_one, Module.End.one_apply]

end PositivityTheory.Rg.Rsw.L.LFixW

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.FixW

section

@[expose] public section

noncomputable section




open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

theorem fixW : IdemEx → GenK → WMaj → FixW := by
  classical
  intro _ hG hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω
  have hHaar : μ.IsAddHaarMeasure := by
    obtain ⟨_, h, -⟩ := hμ
    exact h
  obtain ⟨S1, hS1⟩ := LFixW.fixN V hψ
  obtain ⟨S2, hS2⟩ := LFixW.fixWc V hψ
  obtain ⟨S3, hS3⟩ := LFixW.unit_triv D χ hχ
  obtain ⟨S4, hS4⟩ := hG D n
  refine ⟨S1 ∪ S2 ∪ S3 ∪ S4, fun S hS e he Φ hΦ u hu => ?_⟩
  have h1 : S1 ⊆ S := fun x hx => hS (by simp [hx])
  have h2 : S2 ⊆ S := fun x hx => hS (by simp [hx])
  have h3 : S3 ⊆ S := fun x hx => hS (by simp [hx])
  have h4 : S4 ⊆ S := fun x hx => hS (by simp [hx])
  have hcont := (hWM D n V ψ hψ χ hχ hres θ hθ μ hμ ω hω Φ).1
  have hA : IsClosed {g : G D n | ω g Φ = Φ} := by
    have hEq : {g : G D n | ω g Φ = Φ} = ⋂ x, {g : G D n | (ω g Φ).1 x = Φ.1 x} := by
      ext g
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro h x
        rw [h]
      · intro h
        exact Subtype.ext (funext h)
    rw [hEq]
    exact isClosed_iInter fun x =>
      isClosed_eq (hcont.comp (continuous_id.prodMk continuous_const)) continuous_const
  have h1A : (1 : G D n) ∈ {g : G D n | ω g Φ = Φ} := by
    show ω 1 Φ = Φ
    rw [map_one]
    rfl
  have key := hS4 S h4 {g : G D n | ω g Φ = Φ} hA h1A (by
    intro g hg hcases x hx
    have hx' : ω x Φ = Φ := hx
    show ω (g * x) Φ = Φ
    rw [map_mul]
    show ω g (ω x Φ) = Φ
    rw [hx']
    rcases hcases with hN | hM | ⟨w, u', hw, hu', hu'K, rfl⟩
    · exact hS1 S h1 n θ μ ω χ hω g hg hN Φ (fun y hy => by rw [hΦ y, if_neg hy])
    · exact LFixW.fixM V hω he (hS3 S h3) hg hM Φ hΦ
    · exact hS2 S h2 e he n θ μ ω χ hω hHaar w u' hw hu' hu'K Φ hΦ)
  exact key hu

end PositivityTheory.Rg.Rsw.L

end
end
end
