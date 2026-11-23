module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddA
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddC
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSummableBoundSchwartzMajorantRationalTransStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartzStatement
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
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
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ModerateGrowthSchwartz
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixSchwartzMajorantMeasurableRationalSh
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCommonLevelCompactTranslatesThetaFunction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyUnitaryPairKeepsCompletedLattice
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IdemElt
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddB

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMatrixSchwartzMajorantInvMulLeStatement

section

@[expose] public section

open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar


theorem _root_.GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (n : ℕ) (Q : Set (GA D V)), IsCompact Q → ∀ K : Set (Mx D V.rank n), IsCompact K → ∃ K' : Set (Mx D V.rank n), IsCompact K' ∧ ∀ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ Q, ∀ x : Mx D V.rank n, GlobalTheory.Unf.maj θ K N (HMul.hMul (Formalism.L2.Theta.mt V y⁻¹) x : Mx D V.rank n) ≤ C * GlobalTheory.Unf.maj θ K' N x :=
  @_root_.GlobalTheory.RegSchProj.maj_mt_le
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBddD

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

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χ : (AE D)ˣ →* Circle} {θ : InfFam D}
  {μ : Measure (Mx D W.rank n)} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem theta_cont (hθ : IsInfFam θ) (Φ : schwartzA θ W.rank n)
    (hcont : Continuous fun u : G D n × Mx D W.rank n => (ω u.1 Φ).1 u.2)
    (hmaj : ∀ C : Set (G D n), IsCompact C → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ C, ∀ x, ‖(ω g Φ).1 x‖ ≤ ‖M x‖) :
    Continuous fun u : G D n × GA D W => theta ω Φ u.1 u.2 := by
  refine continuous_iff_continuousAt.2 fun p => ?_
  obtain ⟨Qg, hQg, hpg⟩ := exists_compact_mem_nhds p.1
  obtain ⟨Qh, hQh, hph⟩ := exists_compact_mem_nhds p.2
  obtain ⟨M, hM, hMb⟩ := hmaj Qg hQg
  obtain ⟨N, hN⟩ := GlobalTheory.T.exists_summable_bound_schwartz_majorant_rational_translates D θ hθ W.rank n
  obtain ⟨-, K, hK, hC⟩ := GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant D θ hθ W.rank n M (GlobalTheory.T.isSchwartzBruhatAdelicMatrix_of_mem_adelicSchwartz D θ hθ W.rank n M hM)
  obtain ⟨K', hK', hmul⟩ := GlobalTheory.T.adelicMatrixSchwartzMajorant_inv_mul_le D θ hθ W n Qh hQh K hK
  obtain ⟨C, hC⟩ := hC N
  obtain ⟨C₂, hC₂, hmul'⟩ := hmul N
  obtain ⟨b, hb, hb'⟩ := hN K' {0} hK' isCompact_singleton
  have hterm : ∀ ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      Continuous fun u : G D n × GA D W => (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := fun ξ =>
    hcont.comp (continuous_fst.prodMk (((GlobalTheory.LatNhds.continuous_mt_inv W).comp continuous_snd).matrix_mul
      continuous_const))
  have hon : ContinuousOn (fun u : G D n × GA D W => ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E,
      (ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))) (Qg ×ˢ Qh) := by
    refine continuousOn_tsum (fun ξ => (hterm ξ).continuousOn) (hb.mul_left (|C| * C₂)) fun ξ u hu => ?_
    have h1 := hMb u.1 hu.1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h2 := hC (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    have h3 := hmul' u.2 hu.2 (rat ξ : Mx D W.rank n)
    have h4 := hb' 0 rfl ξ
    rw [zero_add] at h4
    have hm0 := GlobalTheory.Unf.maj_nonneg θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))
    calc ‖(ω u.1 Φ).1 (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n))‖
        ≤ C * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) := h1.trans h2
      _ ≤ |C| * GlobalTheory.Unf.maj θ K N (mt W u.2⁻¹ ⬝ (rat ξ : Mx D W.rank n)) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hm0
      _ ≤ |C| * (C₂ * GlobalTheory.Unf.maj θ K' N (rat ξ : Mx D W.rank n)) := mul_le_mul_of_nonneg_left h3 (abs_nonneg C)
      _ ≤ |C| * (C₂ * b ξ) := by gcongr
      _ = |C| * C₂ * b ξ := by ring
  exact hon.continuousAt (prod_mem_nhds hpg hph)

theorem theta_full (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) {g : G D n}
    (hg : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1) (h : GA D W) :
    theta ω Ψ' g h = ∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1)) := by
  unfold theta
  have hsupp : Function.support (fun ξ : Matrix (Fin W.rank) (Fin n) D.host.E => (ω g Ψ').1 (mm (mt W h⁻¹) (rat ξ))) ⊆
      {y : Matrix (Fin W.rank) (Fin n) D.host.E | y.rank = W.rank} := by
    intro ξ hξ
    by_contra hr
    exact hξ (term_zero hω hnb C hC Ψ Ψ' hΨ hΨ' hg h ξ hr)
  exact (tsum_subtype_eq_of_support_subset hsupp).symm

theorem bound_triv (hω : IsWeilSch ψ χ θ W μ ω) {nb : hermA D n → G D n} (hnb : IsNMap nb) {v : Pl D}
    (C : Cut D n v) (hC : C.Kills ψ W.rank) (Ψ Ψ' : schwartzA θ W.rank n) (hΨ : ∀ k ∈ KAt D n v, ω k Ψ = Ψ)
    (hΨ' : Ψ' = ∑ x ∈ C.s, C.co x • ω (nb x) Ψ) (hLB : LatBound) (hθ : IsInfFam θ)
    (hmaj : ∀ Q : Set (G D n), IsCompact Q → ∃ M ∈ schwartzA θ W.rank n, ∀ g ∈ Q, ∀ x, ‖(ω g Ψ').1 x‖ ≤ ‖M x‖)
    (Q : Set (G D n)) (hQ : IsCompact Q) :
    ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 → ∀ h, ‖theta ω Ψ' g h‖ ≤ b := by
  obtain ⟨M, hM, hMb⟩ := hmaj Q hQ
  obtain ⟨B, hB⟩ := hLB D θ hθ W n M hM
  refine ⟨B, fun g hg hgv h => ?_⟩
  rw [theta_full hω hnb C hC Ψ Ψ' hΨ hΨ' hgv h]
  have e : ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ₑ ≤ B :=
    (enorm_tsum_le_tsum_enorm).trans ((ENNReal.tsum_le_tsum fun y => by
      have := hMb g hg (mm (mt W h⁻¹) (rat y.1))
      rw [← ofReal_norm, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal this).trans (hB h))
  have e2 : ENNReal.ofReal ‖∑' y : {y : Matrix (Fin W.rank) (Fin n) D.host.E // y.rank = W.rank},
      (ω g Ψ').1 (mm (mt W h⁻¹) (rat y.1))‖ ≤ ENNReal.ofReal B := by
    rw [ofReal_norm, ENNReal.ofReal_coe_nnreal]; exact e
  exact (ENNReal.ofReal_le_ofReal_iff B.2).1 e2

end PositivityTheory.Rg.Rsw.L.LThBdd

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LThBdd

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

namespace PositivityTheory.Rg.Rsw.L.LThBdd

variable {D : D7} {n : ℕ} {W : HSp D} {θ : InfFam D} {ω : G D n →* Module.End ℂ (schwartzA θ W.rank n)}

theorem bound_all {v : Pl D} (U : Subgroup (G D n)) (hUo : IsOpen (U : Set (G D n))) (Φ : schwartzA θ W.rank n)
    (hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Φ (γ * g) h = theta ω Φ g h)
    (hfix : ∀ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Φ = Φ)
    (hU : ∀ k k' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k = GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v k' →
      k ∈ U → k' ∈ U)
    (hdec : ∀ g : G D n, ∃ γ ∈ GF D n, ∃ g' : G D n, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g' = 1 ∧
      ∃ k ∈ U, k ∈ atPts D.sp.cm.sig (Jst D n) {v} ∧ g = γ * g' * k)
    (hb : ∀ Q : Set (G D n), IsCompact Q → ∃ b : ℝ, ∀ g ∈ Q, GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v g = 1 →
      ∀ h, ‖theta ω Φ g h‖ ≤ b)
    (K₀ : Set (G D n)) (hK₀ : IsCompact K₀) : ∃ b : ℝ, ∀ g ∈ K₀, ∀ h, ‖theta ω Φ g h‖ ≤ b := by
  have hred : ∀ γ ∈ GF D n, ∀ g' k, k ∈ U → k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ h,
      theta ω Φ (γ * g' * k) h = theta ω Φ g' h := by
    intro γ hγ g' k hk hkv h
    rw [mul_assoc, hrat γ hγ]
    unfold theta
    rw [map_mul, Module.End.mul_apply, hfix k hk hkv]
  choose γf hγf g'f hg'f kf hkf hkvf hgf using hdec
  obtain ⟨W₀, hW₀c, hW₀1, hW₀U⟩ := exists_compact_subset hUo (one_mem U)
  have hW₀n : W₀ ∈ 𝓝 (1 : G D n) := mem_interior_iff_mem_nhds.1 hW₀1
  have hN : ∀ g₀ : G D n, {g | g₀⁻¹ * g ∈ W₀} ∈ 𝓝 g₀ := fun g₀ =>
    (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW₀n)
  obtain ⟨t, -, hcov⟩ := hK₀.elim_nhds_subcover (fun g₀ => {g | g₀⁻¹ * g ∈ W₀}) fun g₀ _ => hN g₀
  let τ : G D n → G D n := fun ε => ε * (locPart v ε)⁻¹
  have hτ : Continuous τ := continuous_id.mul ((continuous_locPart v).inv)
  let Q : Set (G D n) := ⋃ g₀ ∈ t, (fun ε => g'f g₀ * τ ε) '' W₀
  have hQ : IsCompact Q := t.isCompact_biUnion fun g₀ _ => hW₀c.image (continuous_const.mul hτ)
  obtain ⟨b, hb'⟩ := hb Q hQ
  refine ⟨b, fun g hg h => ?_⟩
  obtain ⟨g₀, hg₀t, hgg₀⟩ := Set.mem_iUnion₂.1 (hcov hg)
  set ε := g₀⁻¹ * g with hε
  have hεW : ε ∈ W₀ := hgg₀
  set εv := locPart v ε with hεv
  set ε' := τ ε with hε'
  have hpv : GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v ε' = 1 := by
    show GlobalTheory.AdelicU.proj D.sp.cm.sig (Jst D n) v (ε * (locPart v ε)⁻¹) = 1
    rw [map_mul, map_inv, proj_locPart, mul_inv_cancel]
  have hc : kf g₀ * ε' = ε' * kf g₀ := commute_of_atPts (hkvf g₀) hpv
  have hsplit : ε' * εv = ε := by
    show ε * (locPart v ε)⁻¹ * locPart v ε = ε
    group
  have hkU : kf g₀ * εv ∈ U := mul_mem (hkf g₀) (hU ε εv (proj_locPart v ε).symm (hW₀U hεW))
  have hkv : kf g₀ * εv ∈ atPts D.sp.cm.sig (Jst D n) {v} := mul_mem (hkvf g₀) (locPart_mem_atPts v ε)
  have heq : g = γf g₀ * (g'f g₀ * ε') * (kf g₀ * εv) := by
    calc g = g₀ * ε := by rw [hε]; group
      _ = γf g₀ * g'f g₀ * kf g₀ * (ε' * εv) := by rw [← hgf g₀, hsplit]
      _ = γf g₀ * g'f g₀ * (kf g₀ * ε') * εv := by simp only [mul_assoc]
      _ = γf g₀ * g'f g₀ * (ε' * kf g₀) * εv := by rw [hc]
      _ = _ := by simp only [mul_assoc]
  rw [heq, hred _ (hγf g₀) _ _ hkU hkv]
  refine hb' _ (Set.mem_iUnion₂.2 ⟨g₀, hg₀t, ε, hεW, rfl⟩) ?_ h
  rw [map_mul, hg'f g₀, hpv, one_mul]

end PositivityTheory.Rg.Rsw.L.LThBdd

namespace PositivityTheory.Rg.Rsw.L

open LThBdd in
theorem thBdd : WMaj → LatBound → WeakApproximationFinitePlace → ThBdd := by
  intro hWM hLB hWA D n W ψ hψ χ hχ hη θ hθ μ hμ ω hω nb hnb v C hC Ψ Ψ' hΨ hΨ'
  obtain ⟨𝓕, hμ'⟩ := hμ
  have hW := hWM D n W ψ hψ χ hχ hη θ hθ μ ⟨𝓕, hμ'⟩ ω hω Ψ'
  have hrat : ∀ γ ∈ GF D n, ∀ g h, theta ω Ψ' (γ * g) h = theta ω Ψ' g h :=
    fun γ hγ g h => theta_rat hψ hχ hθ hμ' hω Ψ' hγ g h
  have hfix : ∀ k ∈ Ucut nb v C.s, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ω k Ψ' = Ψ' :=
    fun k hk hkv => fix_open hnb C Ψ Ψ' hΨ hΨ' hk hkv
  refine ⟨theta_cont hθ Ψ' hW.1 hW.2, hrat, ⟨Ucut nb v C.s, isOpen_Ucut _ _ _, hfix⟩, fun K₀ hK₀ => ?_,
    fun x g hg => ⟨omega_cut hω hnb C Ψ Ψ' hΨ' hg, theta_nb hω hnb C hC Ψ Ψ' hΨ hΨ' x hg⟩⟩
  exact bound_all (Ucut nb v C.s) (isOpen_Ucut _ _ _) Ψ' hrat hfix (fun k k' e hk => mem_Ucut_of_proj e hk)
    (fun g => hWA D n v (Ucut nb v C.s) (isOpen_Ucut _ _ _) g)
    (bound_triv hω hnb C hC Ψ Ψ' hΨ hΨ' hLB hθ hW.2) K₀ hK₀

end PositivityTheory.Rg.Rsw.L

end
end
end
