module

public import Formalism.AdmissibleDesigns.TrivialBoundTargetOfDict
public import Formalism.AdmissibleDesigns.URecApply
public import Formalism.AdmissibleDesigns.CycMatchRec
public import Formalism.AdmissibleDesigns.H1MapMemLcH1
public import Formalism.AdmissibleDesigns.TrivialBoundGeneral
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
import Mathlib.Tactic.Linter.Style

-- Source module: Formalism.AdmissibleDesigns.URepApply

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
theorem uRec_smul {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c : Fin (D.R.t + 1))
    (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i)) (a : D.nd.O i) (m : Mc i Dd c) :
    uRec i Dd hw c φ (a • m) = (D.nbr i w hw).eO a • uRec i Dd hw c φ m := by
  rw [uRec_apply, uRec_apply]
  exact (congrArg (koEquiv (D.nbr i w hw).eO (Formalism.MainNotions.N.KHf.eK (D.nbr i w hw))
    (fun x => Br.toLLK_alg (D.nbr i w hw) x)) (φ.map_smul a m)).trans (koEquiv_smul _ _ _ _ _)

theorem uRep_apply' (c : Fin (D.R.t + 1)) (g : GE D.nd) (m : Mc i Dd c) :
    uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m = uElt Dd.r Dd.χ g • m := rfl

omit [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)] in
theorem koE_apply' (e : ℕ) (g : GE D.nd) (x : KO (D.nd.O i)) : koE i e g x = sE i e g • x := rfl

theorem eO_sE (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (e : ℕ) (g : Dw i dc (idx i dc w)) :
    (D.nbr i w hw).eO (sE i e (g : GE D.nd)) = (epsL i dc hw (eW i dc hw g)) ^ e := by
  have hz : (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = ((cycE i (g : GE D.nd))⁻¹) ^ e := by
    rw [show (cycE i ^ (-(e : ℤ))) (g : GE D.nd) = (cycE i (g : GE D.nd)) ^ (-(e : ℤ)) from rfl,
      zpow_neg, zpow_natCast, inv_pow]
  have key : sE i e (g : GE D.nd) = (algebraMap ℤ_[D.nd.l i] (D.nd.O i)
      (((cycE i (g : GE D.nd))⁻¹ : ℤ_[D.nd.l i]ˣ) : ℤ_[D.nd.l i])) ^ e := by
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ← hz]
    rfl
  rw [key, map_pow]
  simp [epsL]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem uRec_act (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (g : Dw i dc (idx i dc w)) (m : Mc i Dd c) :
    uRec i Dd hw c φ (uElt Dd.r Dd.χ (g : GE D.nd) • m) =
      (epsL i dc hw (eW i dc hw g)) ^ ((c : ℕ) - 1) • uRec i Dd hw c φ m := by
  have h1 : uElt Dd.r Dd.χ (g : GE D.nd) • m = sE i ((c : ℕ) - 1) (g : GE D.nd) • m := by
    apply φ.injective
    rw [← uRep_apply' i Dd c, hφ, koE_apply', φ.map_smul]
  rw [h1, uRec_smul, eO_sE i dc hcyc hw]




def coefDictOf (hcyc : CycW i dc) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (φ : Mc i Dd c ≃ₗ[D.nd.O i] KO (D.nd.O i))
    (hφ : ∀ g m, φ (uRep (D.nd.O i) (M := Mc i Dd c) Dd.r Dd.χ g m) = koE i ((c : ℕ) - 1) g (φ m))
    (hcont : Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^ ((c : ℕ) - 1)) :
    CoefDict (Br.PD D.loc D.nbr i w hw) (Br.LLw (D.nbr i w hw)) (Br.Ow (D.nbr i w hw)) (D.nbr i w hw).eO
      (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1) where
  Ce := twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont
  u := uRec i Dd hw c φ
  u_smul a m := uRec_smul i Dd hw c φ a m
  u_act g m := (uRec_act i dc Dd hcyc hw c φ hφ g m).trans
    (actD_twLat Subtype.val_injective (epsL i dc hw) (epsL_eq i dc hcyc hw) ((c : ℕ) - 1) hcont (eW i dc hw g)
      (uRec i Dd hw c φ m)).symm

end Dict

end Formalism.MainNotions.N.K.TBb

end
end
end

-- Source module: Formalism.AdmissibleDesigns.TrivialBoundTargetOfPsi

section

@[expose] public section

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

noncomputable section

open Classical

namespace Formalism.MainNotions.N.K.TBb

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Formalism.WeaklyAdmissibleFiltrations Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.MainNotions.N.K.TB
open Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N.K.ShaT
open Formalism.RepresentationBoundsCohomology.ringDataObjects (RingData RingDef)

section Cyc

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)

theorem cycW_of : CycW i dc := by
  intro w hw g
  have h1 := Formalism.MainNotions.N.KBKa.cycZ_eq_χQ (D.nbr i w hw) (D.loc (D.nd.l i)) (eW i dc hw g)
  have h2 := (D.loc (D.nd.l i)).PD_χ (D.nbr i w hw).Kw (eW i dc hw g)
  have h3 : ((Br.ι (D.nbr i w hw) (eW i dc hw g) : Dec (F := D.host.E) (D.nd.plOm.1 w)) : GE D.nd) = (g : GE D.nd) := by
    show (((D.nbr i w hw).e.symm ((D.nbr i w hw).e (MulEquiv.subgroupCongr (Dw_idx i dc hw) g)) :
      ↥(Dec (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  rw [h3] at h1
  show ((((D.loc (D.nd.l i)).PD (D.nbr i w hw).Kw).χ (eW i dc hw g) : ℚ_[D.nd.l i]ˣ) : ℚ_[D.nd.l i]) = _
  rw [h2, ← h1]
  rfl

theorem eW_inert' {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (h : Br.G D.nbr i w hw) (hh : h ∈ Br.inert D.nbr i w hw) :
    (eW i dc hw).symm h ∈ (Ine (F := D.host.E) (Aw i dc (idx i dc w))).subgroupOf (Dw i dc (idx i dc w)) := by
  rw [Subgroup.mem_subgroupOf]
  have hA : Aw i dc (idx i dc w) = D.nd.plOm.1 w := by
    unfold Aw
    rw [plOf_idx i dc (mem_plSet i dc hw)]
  rw [hA]
  exact hh

end Cyc

section Dict

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

theorem sE_cont (c' : Fin D.R.t) :
    Continuous fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g := by
  have := D.nd.trO i
  have hc1 : Continuous fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := by
    have : (fun g : GE D.nd => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i)) =
        fun g => ((D.nd.chi i 1 g⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) := funext fun g => by rw [map_inv]
    rw [this]
    exact (D.nd.chi_cont i 1).comp continuous_inv
  have h := hc1.mul (D.nd.chi_cont i ((c' : ℕ) + 1))
  have he : (fun g : GE D.nd => sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) g) =
      fun g => (((D.nd.chi i 1 g)⁻¹ : (D.nd.O i)ˣ) : D.nd.O i) * ((D.nd.chi i ((c' : ℕ) + 1) g : (D.nd.O i)ˣ) : D.nd.O i) :=
    funext fun g => (chi_ratio (i := i) c' g).symm
  rw [he]
  exact h

theorem epsL_cont {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i)) (c' : Fin D.R.t) :
    Continuous fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) := by
  have he : (fun h => (algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw)) (epsL i dc hw h)) ^
      (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1)) = fun h => algebraMap (Br.Ow (D.nbr i w hw)) (Br.LLw (D.nbr i w hw))
        ((D.nbr i w hw).eO (sE i (((Fin.succ c' : Fin (D.R.t + 1)) : ℕ) - 1) (((eW i dc hw).symm h : Dw i dc (idx i dc w)) : GE D.nd))) := by
    funext h
    rw [eO_sE i dc (cycW_of i dc) hw, MulEquiv.apply_symm_apply, map_pow]
  rw [he]
  exact continuous_subtype_val.comp ((D.nbr i w hw).eO_cont.comp
    ((sE_cont i c').comp (continuous_subtype_val.comp (eW_symm_cont i dc hw))))

variable [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]



theorem coefDict_of
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ)) :
    Nonempty (CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) := by
  obtain ⟨φ, hφ⟩ := blkTw_of_def hD hN c hc
  have hc0 : c ≠ 0 := by
    intro h
    subst c
    simp at hc
  obtain ⟨c', rfl⟩ : ∃ c', Fin.succ c' = c := Fin.exists_succ_eq.mpr hc0
  exact ⟨coefDictOf i dc Dd (cycW_of i dc) hw c'.succ φ hφ (epsL_cont i dc hw c')⟩

end Dict

section Len

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]



theorem lenMap_of (cB : ℕ) (hTB : TrivialBoundAtRows i dc r π cB) {w : HeightOneSpectrum (𝓞 D.host.E)}
    (hw : w ∈ placesOver D.host.E (D.nd.l i)) (hwrow : w ∈ dc.row) (c : Fin (D.R.t + 1)) (hc : 1 ≤ (c : ℕ))
    (Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
      (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1)) :
    LenMap (Br.PD D.loc D.nbr i w hw) (selfO i hw) (Qcore i dc Dd c (idx i dc w) cB) Cd.Ce cB := by
  have hT := hTB w hw hwrow
  have het : (c : ℕ) - 1 < D.R.t := by
    have := c.2
    omega
  have h2 := trivial_bound_general hT het Cd.Ce
  have hp : (Br.PD D.loc D.nbr i w hw).p = D.nd.l i := Br.PD_p D.loc D.nbr i w hw
  refine lenMap_gen Cd (eW_symm_cont i dc hw) hp ?_ ?_
  · intro z hz hF
    unfold Fc at hF
    split_ifs at hF with h1
    · exact hW_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (fun h hh => eW_inert' i dc hw h hh) z hz hF
    · exact hW_bot Cd z hz hF
  · intro z hz hH
    unfold Fc
    split_ifs with h1
    · exact hB_zero Cd (eW_symm_cont i dc hw) (h2.2 (by omega)) (eW_inert i dc hw) z hz hH
    · exact hB_bot Cd (eW_symm_cont i dc hw) (h2.1 (by omega)) z hz hH

end Len

section Dict2

variable {D : D7} (i : D.nd.Loc) (dc : TruncatedSeriesCountingIdentities.Decl D i)
  (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
  (π : D.nd.X i) (g0 : GE D.nd) (eB e₁ s : D.nd.X i → MatN D.nd i)
  (Dd : RingData (D.nd.O i) (D.nd.X i) (Fin D.R.nV) (GE D.nd) D.R.t (RepresentationBoundsCohomology.blk D.R))
  [∀ k, SMulCommClass Dd.R' (D.nd.O i) (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]
  [∀ k, IsScalarTower Dd.T' Dd.R' (blockRestrictedRepresentationType (RepresentationBoundsCohomology.blk D.R) Dd.ρk k)]

def YtPsi : Prop :=
  ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)), w ∈ dc.row →
    ∀ c : Fin (D.R.t + 1), 1 ≤ (c : ℕ) →
      ∀ Cd : CoefDict (Br.PD D.loc D.nbr i w hw) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1 ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL)
          (selfO i hw) (Mc i Dd c) Dd.r Dd.χ (Dw i dc (idx i dc w)) (eW i dc hw) ((c : ℕ) - 1),
        ∃ Y : YtLat (G := Br.G D.nbr i w hw) (Qp := ℚ_[D.nd.l i]) ↥(TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL.1
            ↥(OL (TruncatedSeriesCountingIdentities.CoefExt.self i w hw).LL),
          YtCrys (PD := Br.PD D.loc D.nbr i w hw) Y (Jr i r π (TruncatedSeriesCountingIdentities.CoefExt.self i w hw)) ∧
          PsiExt (selfO i hw) Dd.r Dd.χ Dd.E (Dw i dc (idx i dc w)) (eW i dc hw) Y Cd



theorem tbDict2_of (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hY : YtPsi i dc r π Dd) : TBDict2 i dc r π Dd cB := by
  intro w hw hwrow c hcc
  obtain ⟨Cd⟩ := coefDict_of i dc r ρ π g0 eB e₁ s Dd hD hN hw c hcc
  obtain ⟨Y, hY1, hY2⟩ := hY w hw hwrow c hcc Cd
  refine ⟨Y, Cd, hY1, hY2, ?_, ?_⟩
  · exact yLoc_of i dc r π g0 eB e₁ s Dd hD hc c (idx i dc w)
  · exact lenMap_of i dc r π Dd cB hTB hw hwrow c hcc Cd

theorem trivial_bound_target_of_psi (cB : ℕ)
    (hD : RingDef (D.nd.O i) (D.nd.T i) (RepresentationBoundsCohomology.repX D.nd r) π (chiU D.nd i 1) (epsU D.nd i) g0 eB e₁ s Dd)
    (hN : RepresentationBoundsCohomology.NormAt D.nd r ρ π) (hc : Formalism.MainNotions.TruncatedSeriesCountingIdentities.FamilyContinuous (D := D) i r) (hTB : TrivialBoundAtRows i dc r π cB)
    (hTie : TruncatedSeriesCountingIdentities.LocalCoefficientCompatibility i) (hY : YtPsi i dc r π Dd) : TBTarget i dc Dd cB :=
  trivial_bound_target_of_dict i dc r π Dd cB hTB hTie (tbDict2_of i dc r ρ π g0 eB e₁ s Dd cB hD hN hc hTB hY)

end Dict2

end Formalism.MainNotions.N.K.TBb

end
end
end
