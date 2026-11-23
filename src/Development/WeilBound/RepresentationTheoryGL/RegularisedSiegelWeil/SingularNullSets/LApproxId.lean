module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdB
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdS
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinateFormSymmetricNondegenerateStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HCoContinuousAddEquivStatement
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPairingInCoordinatesStatement
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.CharSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordForm
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIdemEx
public import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
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
import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology
import Mathlib.RingTheory.PicardGroup

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MemOfCoord

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

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem memHA (D : D7) (t : ℕ) (X : Mx D t t) : X ∈ hermA D t ↔ X ∈ HermR (AF D.host.F) D.sp.cm.sig t := by
  constructor
  · intro h a c
    have h' : GlobalTheory.MixModel.adj X = X := h
    have := congrFun (congrFun h' a) c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using this
  · intro h
    change GlobalTheory.MixModel.adj X = X
    ext a c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using h a c

theorem smul_memA (D : D7) (t : ℕ) (e : AE D) (he : cA D e = e) (X : Mx D t t) (h : X ∈ hermA D t) :
    e • X ∈ hermA D t := by
  have h' : GlobalTheory.MixModel.adj X = X := h
  change GlobalTheory.MixModel.adj (e • X) = e • X
  ext a c
  have := congrFun (congrFun h' a) c
  simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, he] at this ⊢
  rw [this]

theorem pch_eq (D : D7) (t : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (X T : Mx D t t) (hX : X ∈ hermA D t)
    (hT : T ∈ hermA D t) :
    pch ψ X T = ψ (pairHerm (AF D.host.F) D.sp.cm.sig t ⟨X, (memHA D t X).1 hX⟩ ⟨T, (memHA D t T).1 hT⟩) := by
  simp only [pch, halfTr, trA, pairHerm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem coord_fix (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (X : HermR (AF D.host.F) D.sp.cm.sig t) (hX : e • X.1 = X.1) (i : Idx t d) :
    ε * hCo (AF D.host.F) D.sp.cm.sig b X i = hCo (AF D.host.F) D.sp.cm.sig b X i :=
  (hCo_smul _ b ε X X (by rw [← heS, hX]) i).symm

theorem mem_of_coord (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) (y : HermR (AF D.host.F) D.sp.cm.sig t)
    (hw : ∀ i, ε * eA y i = eA y i) : e • y.1 = y.1 := by
  have hyA : y.1 ∈ hermA D t := (memHA D t y.1).2 y.2
  have hY := (memHA D t _).1 (smul_memA D t e hcA y.1 hyA)
  have h1 : eA ⟨e • y.1, hY⟩ = eA y := by
    funext i
    rw [heA, hCo_smul _ b ε y ⟨e • y.1, hY⟩ (by rw [← heS]) i, ← heA, hw]
  exact congrArg Subtype.val (eA.injective h1)



theorem exTheta' (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) :
    ∃ Θ : hermS D t e ≃ₜ+ (Idx t d → fixE ε),
      ∀ x i, ((Θ x i) : AF D.host.F) = eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := by
  have hfix : ∀ (x : hermS D t e) i, ε * eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i =
      eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := fun x i => by
    rw [heA]; exact coord_fix D t e ε heS b ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ x.2 i
  have hinv : ∀ v : Idx t d → fixE ε, e • (eA.symm (fun i => (v i).1)).1 = (eA.symm (fun i => (v i).1)).1 :=
    fun v => mem_of_coord D t e ε heS hcA b eA heA _ (fun i => by rw [eA.apply_symm_apply]; exact (v i).2)
  refine ⟨{ toFun := fun x i => ⟨eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i, hfix x i⟩
            invFun := fun v => ⟨⟨(eA.symm (fun i => (v i).1)).1, (memHA D t _).2 (eA.symm _).2⟩, hinv v⟩
            left_inv := fun x => by
              apply Subtype.ext; apply Subtype.ext
              simp
            right_inv := fun v => by
              funext i
              apply Subtype.ext
              simp
            map_add' := fun x y => by
              funext i
              apply Subtype.ext
              change eA _ i = eA _ i + eA _ i
              exact congrFun (map_add eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ ⟨y.1.1, (memHA D t y.1.1).1 y.1.2⟩) i
            continuous_toFun := continuous_pi fun i => Continuous.subtype_mk ((continuous_apply i).comp
              (eA.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))) _
            continuous_invFun := ((continuous_subtype_val.comp (eA.symm.continuous.comp
              (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _).subtype_mk _ },
    fun x i => rfl⟩

theorem e_eq (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) ((1, LIdemEx.indS S) : AF D.host.F) := by
  have h : e = LIdemEx.eS S := LIdemEx.ae_ext _ _ (fun w => by rw [he.1 w, (LIdemEx.isIdem_eS S).1 w])
    (fun v => by rw [he.2 v, (LIdemEx.isIdem_eS S).2 v])
  exact h.trans rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdD

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

namespace PositivityTheory.Rg.Rsw.L.LApproxId

theorem small_eventually {ι A M : Type} [Finite ι] [TopologicalSpace A] [Zero A] [TopologicalSpace M]
    (R : (ι → A) → M) (hR : Continuous R) (U : Set M) (hU : IsOpen U) (h0 : R 0 ∈ U) (Sp : ℕ → Set A)
    (hSp : Tendsto Sp atTop (𝓝 0).smallSets) : ∀ᶠ k in atTop, ∀ w : ι → A, (∀ i, w i ∈ Sp k) → R w ∈ U := by
  have hW : R ⁻¹' U ∈ 𝓝 (0 : ι → A) := hR.continuousAt.preimage_mem_nhds (hU.mem_nhds h0)
  rw [nhds_pi, Filter.mem_pi] at hW
  obtain ⟨I, -, tt, htt, hsub⟩ := hW
  have hN : (⋂ i, tt i) ∈ 𝓝 (0 : A) := Filter.iInter_mem.mpr htt
  filter_upwards [tendsto_smallSets_iff.mp hSp _ hN] with k hk w hw
  exact hsub (fun i _ => Set.mem_iInter.mp (hk (hw i)) i)

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN in


theorem approxId_of (h1 : OneD) : ApproxId := by
  classical
  intro D t ψ hψ S e he lam hlam
  have hCM : IsCMExt D.host.F D.host.E D.sp.cm.sig := isCMExt_host D
  have : Module.Finite D.host.F D.host.E := Module.finite_of_finrank_eq_succ (n := 1) hCM.2.2.1
  have : BorelSpace (AF D.host.F) := ⟨rfl⟩
  have : BorelSpace (Mx D t t) := ⟨rfl⟩
  obtain ⟨eA, heA⟩ := GlobalTheory.T.exists_homeomorph_hermR_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  obtain ⟨-, hBd⟩ := GlobalTheory.T.coordinate_form_symmetric_nondegenerate D.host.F D.host.E D.sp.cm.sig hCM _ (Module.finBasis D.host.F D.host.E) t
  have hpair := GlobalTheory.T.hermitian_pairing_in_coordinates D.host.F D.host.E D.sp.cm.sig hCM (AF D.host.F) _ (Module.finBasis D.host.F D.host.E) t
  generalize Module.finBasis D.host.F D.host.E = b at heA hBd hpair
  have hε0 : IsIdF S ((1, LIdemEx.indS S) : AF D.host.F) := ⟨rfl, fun v => rfl⟩
  obtain ⟨ε, hε, heS⟩ : ∃ ε : AF D.host.F, IsIdF S ε ∧ e = algebraMap (AF D.host.F) (AE D) ε :=
    ⟨_, hε0, e_eq D S e he⟩
  have hcA : cA D e = e := (LIdemEx.idem_props S e he).2
  obtain ⟨Θ, hΘ⟩ := exTheta' D t e ε heS hcA b eA heA
  have hcl : IsClosed ((fixE ε : AddSubgroup (AF D.host.F)) : Set (AF D.host.F)) :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_id
  have : LocallyCompactSpace (fixE ε) := hcl.locallyCompactSpace
  have : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨g1, G1, Sp, hg, hlim, hsupp, hSp⟩ := h1 D.host.F hCM.1 ψ hψ S ε hε (Measure.addHaar) inferInstance
  obtain ⟨c, -, hTr⟩ := transfer Θ lam (Measure.addHaar : Measure (fixE ε))
  set Bm := (coordForm D.sp.cm.sig b t).map (algebraMap D.host.F (AF D.host.F)) with hBm
  let sT : Mx D t t → _ := fun T => if hT : T ∈ hermA D t then
    Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hT⟩ else 0
  refine ⟨fun k x => ∏ i, g1 k (Θ x i), fun k T => if T ∈ hermA D t then (c : ℝ) * ∏ i, G1 k (sT T i) else 0,
    fun k => ⟨?_, ?_, fun T hT => ⟨?_, ?_⟩⟩, fun x => ?_, ?_⟩
  · exact (hTr (fun _ => g1 k)).2 (fun _ => (hg k).1)
  · intro x
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun i _ => (hg k).2.1 _)
  · beta_reduce
    rw [if_pos hT]
    exact mul_nonneg c.2 (Finset.prod_nonneg fun i _ => ((hg k).2.2 _).1)
  · beta_reduce
    have hpt : ∀ x : hermS D t e, pch ψ x.1.1 T = ∏ i, ψ ((Θ x i).1 * sT T i) := by
      intro x
      rw [pch_eq D t ψ x.1.1 T x.1.2 hT, hpair, dotProduct, char_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [sT, dif_pos hT, hΘ, heA]
    calc ∫ x, (∏ i, g1 k (Θ x i)) * pch ψ x.1.1 T ∂lam
        = ∫ x, ∏ i, (fun i h => g1 k h * ψ (h.1 * sT T i)) i (Θ x i) ∂lam := by
          congr 1; funext x; rw [hpt, ← Finset.prod_mul_distrib]
      _ = (c : ℂ) * ∏ i, ∫ h, g1 k h * ψ (h.1 * sT T i) ∂(Measure.addHaar : Measure (fixE ε)) :=
          (hTr (fun i h => g1 k h * ψ (h.1 * sT T i))).1
      _ = _ := by
          rw [if_pos hT]
          push_cast
          congr 1
          exact Finset.prod_congr rfl fun i _ => ((hg k).2.2 _).2
  · have := tendsto_finsetProd Finset.univ (fun i _ => hlim (Θ x i))
    simpa using this
  · intro C hC hCT ε' hε'
    have hunit : IsUnit Bm.det := by
      have h := (RingHom.map_det (algebraMap D.host.F (AF D.host.F)) (coordForm D.sp.cm.sig b t)).symm
      rw [hBm]
      exact h ▸ (isUnit_iff_ne_zero.mpr hBd).map _
    let R : (Idx t (Module.finrank D.host.F D.host.E) → AF D.host.F) → Mx D t t := fun w => (eA.symm (Bm⁻¹ *ᵥ w)).1
    have hRc : Continuous R :=
      continuous_subtype_val.comp (eA.symm.continuous.comp (continuous_const.matrix_mulVec continuous_id))
    have hU : IsOpen {M : Mx D t t | -M ∉ C} := hC.isOpen_compl.preimage continuous_neg
    have h0 : R 0 ∈ {M : Mx D t t | -M ∉ C} := by
      have : R 0 = 0 := by simp [R, Matrix.mulVec_zero]
      simp only [Set.mem_ofPred_eq, this, neg_zero]
      exact fun h => (hCT 0 h).2.2 rfl
    filter_upwards [small_eventually R hRc _ hU h0 Sp hSp] with k hk T hTC
    obtain ⟨hTA, heT, -⟩ := hCT T hTC
    by_contra hlt
    have hpos := lt_trans hε' (not_le.mp hlt)
    beta_reduce at hpos
    rw [if_pos hTA] at hpos
    have hprod : ∀ i, G1 k (sT T i) ≠ 0 := fun i =>
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hpos.ne') i (Finset.mem_univ i)
    have hfixT : ∀ i, ε * sT T i = sT T i := by
      intro i
      simp only [sT, dif_pos hTA, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_left_comm, coord_fix D t e ε heS b _ heT j]
    have hw : ∀ i, -(sT T i) ∈ Sp k := fun i => by
      have := hsupp k (sT T i) (hprod i)
      rwa [hfixT] at this
    have hmem := hk (fun i => -(sT T i)) hw
    have hR : R (fun i => -(sT T i)) = -T := by
      have h2 : (fun i => -(sT T i)) = -(Bm *ᵥ hCo (AF D.host.F) D.sp.cm.sig b ⟨T, (memHA D t T).1 hTA⟩) := by
        funext i; simp only [sT, dif_pos hTA, Pi.neg_apply]
      simp only [R, h2, Matrix.mulVec_neg, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec,
        map_neg, ← heA, eA.symm_apply_apply]
      rfl
    simp only [hR, neg_neg] at hmem
    exact hmem hTC

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end
end

-- Source module: Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxId

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

namespace PositivityTheory.Rg.Rsw.L

theorem approxId : IdemEx → ApproxId := fun _ => LApproxId.approxId_of LApproxId.oneD

end PositivityTheory.Rg.Rsw.L

end
end
end
