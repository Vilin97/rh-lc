module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SglobDzBigDef
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CharacterChoiceData
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DepthZeroSupercuspidalCuspidalModule
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTypePlaceCompletionIdent
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.RingTheory.PicardGroup
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GaloisRepLocalGlobalCompatible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MClassMapD
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasLabelOfIsCuspOf
public import Development.DiscreteGroups.GlobalIrreducibility.IneEqOfHasGreenLe
public import Development.DiscreteGroups.GlobalIrreducibility.LocTypeOfSerParamLe
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVector
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemChainVecsDet
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Mathlib.Algebra.AffineMonoid.UniqueSums
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.GroupTheory.Nilpotent
public import Development.DiscreteGroups.GlobalIrreducibility.SerLocOfTiesLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameParamRecordLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TameSupportCompatible

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelign

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.IneUnrTwist

open Formalism.MainNotions Formalism.ConjugateSelfDual GlobalTheory.WeilDeligne ReciprocityTheory.Gal NumberField IsDedekindDomain TensorProduct

theorem wd_inePol_twist {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} (a χ : WD h) (h1 : χ.lpDim = 1)
    (hu : χ.unr) {s : G E Ω} (hs : s ∈ Ine (F := E) B) : (a.lpChar χ).inePol s = a.inePol s := by
  induction a using WD.ind with | hP n a => ?_
  induction χ using WD.ind with | hP m c => ?_
  rw [WD.lpDim_mk] at h1
  rw [WD.unr_mk] at hu
  rw [WD.lpChar_mk, WD.inePol_of_mem_Ine _ hs, WD.inePol_of_mem_Ine _ hs, WD.charPol_mk, WD.charPol_mk,
    WDRep.tensor_ρ, hu.2]
  let e : (Fin m → ℂ) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simpa using h1)
  let E' := (TensorProduct.congr (LinearEquiv.refl ℂ (Fin n → ℂ)) e).trans (TensorProduct.rid ℂ _)
  rw [← LinearEquiv.charpoly_conj E']
  congr 1
  refine LinearMap.ext fun v => ?_
  simp [E', LinearEquiv.conj_apply]

theorem main : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := fun D T w a χ h1 hu s hs => by
  rw [T.inePol w _ s hs, T.inePol w _ s hs, T.char w a χ h1]
  exact wd_inePol_twist _ _ ((T.dim w χ).trans h1) ((T.unr w χ).1 hu) hs

end GlobalTheory.IneUnrTwist
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaInvariantUnderUnramifiedTwistOfWeilDelignStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

theorem _root_.GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne : ∀ (D : D7), GlobalTheory.RowTie.WDTie D.nd D.naut → IneUnr D := by
  first | exact @GlobalTheory.IneUnrTwist.main | exact GlobalTheory.IneUnrTwist.main | (intros; apply GlobalTheory.IneUnrTwist.main <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSeriesVectorMulOfParahoricBlockCharVectorStatement

section

@[expose] public section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

theorem _root_.GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (a b : ℕ) (χ : (ZMod g)ˣ →* ℂˣ) (h f : (ZMod g)[X]) (v : V), n = a + b → CharIn S χ b h → IsParVec π a b χ v → actTop π a b (S.e a f) v ≠ 0 → Has S π (f * h) := by
  first | exact @GlobalTheory.SerSys.ParVec.has_mul_of_isParVec | exact GlobalTheory.SerSys.ParVec.has_mul_of_isParVec | (intros; apply GlobalTheory.SerSys.ParVec.has_mul_of_isParVec <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOfRootsBarEq

section

@[expose] public section

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.SerLocal

variable (D : D7)

theorem inePol_zero (w : PlE D.host) (s) (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (D.naut.lpZero w) s = 1 := by
  rw [((D.naut.unr_iff_ine _).1 (D.naut.lpZero_unr w)).2 s hs, D.naut.lpDim_zero, pow_zero]

theorem inePol_foldr {ι : Type} {w : PlE D.host} (F : ι → D.naut.LP w) (l : List ι) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (l.foldr (fun x acc => D.naut.lpSum (F x) acc) (D.naut.lpZero _)) s =
      (l.map fun x => D.naut.inePol (F x) s).prod := by
  induction l with
  | nil => simpa using inePol_zero D w s hs
  | cons x l ih => rw [List.foldr_cons, D.naut.inePol_sum, ih, List.map_cons, List.prod_cons]

theorem inePol_speh (p : Part D.naut.CG) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (spehLoc D.nd D.naut p w) s = D.naut.inePol (D.naut.locG p.π w) s ^ p.d := by
  have e : spehLoc D.nd D.naut p w = (List.range p.d).foldr (fun (j : ℕ) acc =>
      D.naut.lpSum (D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w) := by
    simp only [spehLoc, bind_pure_comp, List.map_eq_map, List.foldr_map]
  rw [e, inePol_foldr D (fun k : ℕ => D.naut.lpTw (D.naut.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) _ s hs]
  simp [D.naut.inePol_tw _ _ s hs]

theorem inePol_iso (P : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut P w) s =
      (P.map fun p => D.naut.inePol (D.naut.locG p.π w) s ^ p.d).prod := by
  rw [isoLoc, inePol_foldr D (fun p => spehLoc D.nd D.naut p w) _ s hs]
  simp only [inePol_speh D _ w s hs]

theorem inePol_twist (hU : IneUnr D) (i : D.nd.Loc) (Sig : List (Part D.naut.CG)) (w : PlE D.host) (s)
    (hs : s ∈ ReciprocityTheory.Gal.Ine (F := D.host.E) (D.nd.plOm.1 w)) :
    D.naut.inePol (isoLoc D.nd D.naut
      (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) w) s =
      D.naut.inePol (isoLoc D.nd D.naut Sig w) s * D.naut.inePol (D.naut.locG (D.naut.muC i) w) s ^ D.R.t := by
  rw [inePol_iso D _ w s hs, inePol_iso D _ w s hs, twistIso, List.map_map]
  have e : ∀ {a} (π : D.naut.CG a), D.naut.inePol (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) s =
      D.naut.inePol (D.naut.locG π w) s := fun π => by
    rw [D.naut.locG_tw]
    exact hU w _ _ (D.naut.locG_dim _ w) (D.naut.etaTinv_def w).1 s hs
  simp [Function.comp_def, e, muPart]

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem eq_of_rootsBar_eq {f f' : (ZMod g)[X]} (hf : f.Monic) (hf' : f'.Monic)
    (h : Formalism.CyclotomicNorms.rootsBar f = Formalism.CyclotomicNorms.rootsBar f') : f = f' := by
  apply Polynomial.map_injective (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g)) (RingHom.injective _)
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (hf.map _),
    (IsAlgClosed.splits (f'.map _)).eq_prod_roots_of_monic (hf'.map _)]
  exact congrArg (fun m => (Multiset.map (fun x => X - C x) m).prod) h

theorem rootsBar_pow (c : ZMod g) (t : ℕ) :
    Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) = t • {algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c} := by
  rw [Formalism.CyclotomicNorms.rootsBar, Polynomial.map_pow, Polynomial.map_sub, map_X, map_C, roots_pow, roots_X_sub_C]

theorem eq_of_teich (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ) (hτ : Function.Injective τ) {f f' : (ZMod g)[X]} (hf : f.Monic)
    (hf' : f'.Monic) (c : ZMod g) (t : ℕ)
    (h : ((Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t)).map fun x => X - C (τ x)).prod =
      ((Formalism.CyclotomicNorms.rootsBar f').map fun x => X - C (τ x)).prod *
        (X - C (τ (algebraMap (ZMod g) (Formalism.CyclotomicNorms.Fbar g) c))) ^ t) : f = f' := by
  have h0 : f * (X - C c) ^ t ≠ 0 := (hf.mul ((monic_X_sub_C c).pow t)).ne_zero
  have hm : Formalism.CyclotomicNorms.rootsBar (f * (X - C c) ^ t) = Formalism.CyclotomicNorms.rootsBar f + Formalism.CyclotomicNorms.rootsBar ((X - C c) ^ t) := by
    unfold Formalism.CyclotomicNorms.rootsBar
    rw [Polynomial.map_mul, roots_mul]
    rw [← Polynomial.map_mul]
    exact Polynomial.map_ne_zero h0
  rw [hm, rootsBar_pow, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_nsmul, Multiset.prod_nsmul,
    Multiset.map_singleton, Multiset.prod_singleton] at h
  have h2 := mul_right_cancel₀ (pow_ne_zero t (X_sub_C_ne_zero _)) h
  have h3 := congrArg Polynomial.roots h2
  have e : ∀ m : Multiset (Formalism.CyclotomicNorms.Fbar g),
      ((m.map fun x => X - C (τ x)).prod).roots = m.map τ := fun m => by
    rw [← roots_multiset_prod_X_sub_C (m.map τ), Multiset.map_map]; rfl
  rw [e, e] at h3
  exact eq_of_rootsBar_eq hf hf' (Multiset.map_injective hτ h3)

end Roots

theorem serLoc : ∀ (D : D7) (S : ∀ k, @Sys (D.host.g k) ⟨D.host.g_prime k⟩),
    (∀ k f, D.ntypes.eSer k f = @Sys.e _ ⟨D.host.g_prime k⟩ (S k) D.R.r f) → IneUnr D → LocType D S →
    SerLoc D := by
  intro D S hS hU hL i σ' k v f F hF hne
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hex : ∃ P Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
      IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv) ∧
      ∃ F' ∈ D.naut.typeV i P,
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f)) F' ≠ 0 := by
    by_contra hno
    push Not at hno
    apply hne
    rw [D.mtpar_tie i σ'] at hF
    have hle : (⨆ P ∈ {P | ∃ Sig, (∀ w, isoLoc D.nd D.naut Sig w = D.ntypes.locPar σ' w) ∧
        IsBCV D.nd D.naut i P (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv)},
        D.naut.typeV i P) ≤
        LinearMap.ker (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (atPlace D k v (D.ntypes.eSer k f))) :=
      iSup₂_le fun P ⟨Sig, h1, h2⟩ F' hF' => hno P Sig h1 h2 F' hF'
    exact hle hF
  obtain ⟨P, Sig, hSig, hBC, F', hF', hne'⟩ := hex
  obtain ⟨π, χ, c, h1, h2, h3, h4⟩ := hL i P k v
  obtain ⟨u, hu, hu'⟩ := h1 F' hF' (D.ntypes.eSer k f)
    (Subalgebra.mem_center_iff.2 fun b => (D.ntypes.eSer_central k f b).symm) hne'
  rw [hS] at hu'
  have hmon : f.Monic := ((S k).label D.R.r f (fun h0 => hu' (by rw [h0]; simp [actTop]))).1
  have hHas := GlobalTheory.T.hasSeriesVector_mul_of_parahoricBlockCharVector _ (S k) _ _ π.ρ D.R.r D.R.t χ _ f u rfl h2 hu hu'
  have h5 := h4 _ hHas
  have hs := D.ntypes.tg_mem k v
  rw [← hBC.2.2.2.1 _ (GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v), inePol_twist D hU i Sig _ _ hs, hSig, h3,
    D.ntypes.inertiaCharpoly_type k v _ (by
      rw [← D.ntypes.labPar_def, (D.ntypes.labPar_monic k σ' v).2, D.ntypes.locPar_dim]),
    ← D.ntypes.labPar_def] at h5
  exact eq_of_teich _ (GlobalTheory.TameLabels.teich_injective _ (D.ntypes.teichC_inj k)) hmon (D.ntypes.labPar_monic k σ' v).1 c _ h5.symm

end GlobalTheory.SerLocal
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocTypeOfSerParamLe

section

@[expose] public section



section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.factTypePrime
variable {g : ℕ} [Fact g.Prime]
theorem locType_of_serParamLe_alt {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (hP : ∀ k v, SerParamLe D.R.nV (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ le_rfl π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 (one_le_nV D) _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)
theorem locType_of_labTie_locComp_labParamLe {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) :
    LocType D S :=
  _root_.DiscreteGroups.sglob.DzType.Rt.locType_of_serParamLe_alt hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from _root_.funext fun n => _root_.funext (hS k n)]
    exact hP k v
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SerLocOfTiesLe

section

@[expose] public section



section
noncomputable section
namespace DiscreteGroups.sglob.DzType.Rt
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.TypeLeaf GlobalTheory.SerSys GlobalTheory.SerSys.Bridge
open scoped Classical
attribute [local instance] GlobalTheory.SerSys.Bridge.factT
theorem serLocLe_of_alt (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc) (hP : LabParamLe D.R.nV D L rc) : SerLoc D :=
  have hS : ∀ k, (OfLabel.ofLabel (L k) (five_le D k) hG).IsOf (L k) := fun _ _ _ => rfl
  GlobalTheory.SerLocal.serLoc D _ (hL.sysTie hS) hU (_root_.DiscreteGroups.sglob.DzType.Rt.locType_of_labTie_locComp_labParamLe hL hS hC hP)
theorem serLoc_of_tame_param_le (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) (hG : Green)
    (hL : LabTie D L) (hU : IneUnr D) (hC : _root_.GlobalTheory.SerSys.LocalCompatibility D rc)
    (h1 : ∀ k v, TameGen.SupportCompat (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2))
    (h2 : ∀ k, TameGen.DepthZeroCuspidal (D.host.g k))
    (h3 : ∀ k v, TameParamLe D.R.nV (L k) (fun a => D.naut.inePol a (D.ntypes.tg k v))
      (fun π : GLRep _ => rc k v π.1 π.2)) : SerLoc D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.serLocLe_of_alt D L rc hG hL hU hC (labParamLe_of D L rc hG h1 h2 h3)
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end

-- Source module: Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DepthZeroTypeGlobalOfSeriesLocal

section

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG
namespace DiscreteGroups.sglob.DzType.Rt
theorem depthZeroType_series_local_explicit_alt : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing →
    _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D)
    (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L →
    (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k),
      TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) →
    GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D := by
  intro hPr hG hZ hDZ hL D P L hLT hκ hCen
  obtain ⟨I⟩ := GlobalTheory.TypeIdent.nonempty_ident D
  obtain ⟨rc, hrc, hcl⟩ := _root_.UpperTheory.One.M.exists_isRc_isClassMapD_alt hL D P.T I
  refine _root_.DiscreteGroups.sglob.DzType.Rt.serLoc_of_tame_param_le D L rc hG hLT (GlobalTheory.T.inertiaInvariantUnderUnramifiedTwist_of_weilDeligne D P.T)
    (_root_.GlobalTheory.T.locComp_of_isRc_of_classMap_of_cenLoc hPr hL D P I rc hrc hcl hCen) (_root_.GlobalTheory.T.tame_gen_support_compat_of_is_rc hZ hL D P.T I rc hrc)
    (fun k => GlobalTheory.DepthZeroCusp.depthZeroCuspidal (D.host.g k)) ?_
  intro k v
  obtain ⟨κ, hκ'⟩ := hκ k v
  exact _root_.DiscreteGroups.sglob.DzType.Rt.tame_param_le_of_tame_coupled hDZ hL D P.T I rc hrc L k v κ hκ'

theorem serLoc_of_tame_coupled_and_cenLoc : _root_.GlobalTheory.NRows.ThetaLocalInputsAlt → Green → GlobalTheory.Published.ZelevinskyPolynomialRing → _root_.DiscreteGroups.sglob.DzType.DepthZeroInertiaBigAlt → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (L : ∀ k, LabelDatum (D.host.g k)), LabTie D L → (∀ k v, ∃ κ : IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k), TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) κ (D.ntypes.tg k v) (L k).gen) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → GlobalTheory.TypeLeaf.SerLoc D :=
  _root_.DiscreteGroups.sglob.DzType.Rt.depthZeroType_series_local_explicit_alt
end DiscreteGroups.sglob.DzType.Rt
end
end
end
end
