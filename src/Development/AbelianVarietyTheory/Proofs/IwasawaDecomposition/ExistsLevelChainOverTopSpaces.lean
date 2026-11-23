module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHilbertChainOfLevelOverTopsStatement
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.CompletePartialOrder
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
import Development.AbelianVarietyTheory.Definitions.Foundations.RootOfUnityEightQMemCoeffGaloisSubfield
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Formalism.LocalToGlobal.GaloisLevelStructure.Checks
public import Formalism.LocalToGlobal.IndefiniteReal.IsotInLeOfIntw
public import Formalism.LocalToGlobal.IndefiniteReal.LinIndepOfOrth
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumsEqPairingsTopChainLiftsStatement
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linter.HaveILetI

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalBasisAdapted

section

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem exists_orthonormalBasis_adapted (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (I : Type) [Fintype I] [DecidableEq I] (p : I → Submodule ℂ E)
    (htop : (⨆ i, p i) = ⊤) (horth : ∀ i j, i ≠ j → p i ⟂ p j) :
    ∃ (b : OrthonormalBasis (Fin (Module.finrank ℂ E)) ℂ E) (ty : Fin (Module.finrank ℂ E) → I),
      ∀ i, Submodule.span ℂ (b '' {σ | ty σ = i}) = p i := by
  classical
  have hV : OrthogonalFamily ℂ (fun i => p i) (fun i => (p i).subtypeₗᵢ) :=
    OrthogonalFamily.of_pairwise (fun i j h => horth i j h)
  have hint : DirectSum.IsInternal p :=
    (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top p).2 ⟨hV.independent, htop⟩
  let v : ∀ i, OrthonormalBasis (Fin (Module.finrank ℂ (p i))) ℂ (p i) :=
    fun i => stdOrthonormalBasis ℂ (p i)
  let c := hint.collectedOrthonormalBasis hV v
  have hc : ∀ a : (Σ i, Fin (Module.finrank ℂ (p i))), c a = (v a.1 a.2 : E) := by
    intro a
    simp [c, DirectSum.IsInternal.collectedOrthonormalBasis, DirectSum.IsInternal.collectedBasis_coe]
  have hcard : Fintype.card (Σ i, Fin (Module.finrank ℂ (p i))) = Module.finrank ℂ E :=
    (Module.finrank_eq_card_basis c.toBasis).symm
  let e : (Σ i, Fin (Module.finrank ℂ (p i))) ≃ Fin (Module.finrank ℂ E) :=
    Fintype.equivFinOfCardEq hcard
  refine ⟨c.reindex e, fun σ => (e.symm σ).1, fun i => ?_⟩
  have himg : (c.reindex e) '' {σ | (e.symm σ).1 = i}
      = (p i).subtype '' Set.range (v i).toBasis := by
    ext x
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      rw [OrthonormalBasis.reindex_apply, hc]
      simp only [Set.mem_ofPred_eq] at hσ
      generalize e.symm σ = a at hσ
      obtain ⟨j, k⟩ := a
      subst hσ
      exact ⟨v j k, ⟨k, by simp⟩, rfl⟩
    · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
      refine ⟨e ⟨i, k⟩, by simp, ?_⟩
      rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hc]
      simp
  rw [himg, ← Submodule.map_span, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.Mem
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypePartsSpanAndOrthogonal

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesRows

theorem parts_span_orth : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ b : Bool, (⨆ π, y.prtE F.lv2 b (rep π)) = (y.C F.lv2).EEc b ∧ ∀ π π', π ≠ π' → ∀ x ∈ y.prtE F.lv2 b (rep π), ∀ x' ∈ y.prtE F.lv2 b (rep π'), (y.C F.lv2).ipE b x x' = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 b)) h0.1.1 h0.2
  obtain ⟨s, c, hsG, he⟩ : ∃ (s : Finset (GA D (Yc D 0))) (c : GA D (Yc D 0) → ℂ), (∀ g ∈ s, g ∈ GfC (Yc D 0)) ∧
      R.e0 = ∑ g ∈ s, c g • principalLevelFrame.rtA g :=
    GlobalTheory.Mem.R3.IsotIndep.gaL_finSum (Yc D 0) (R.βY 0) (R.dat0 R.triv) R.eG _
  have key := GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) y.PY y.hF (R.βY 0) (R.dat0 (R.levR F.lv2 b)) R.e0
    (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 hI (D.sp.Y_sig _) hB.models.inf y.stdPsi.1 hs.1 hs.2 ⟨s, c, hsG, he⟩

  set J := levS _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hJ
  set χ := levChi _ (R.βY 0) (R.dat0 (R.levR F.lv2 b)) with hχ

  have hcc : ∀ ρ : Formalism.L2.NG.FinTyp D.host.E D.R.r, (principalLevelFrame.FinTyp.conjT (principalLevelFrame.FinTyp.conjT ρ)).Iso ρ := by
    intro ρ
    unfold Formalism.L2.NG.FinTyp.Iso
    rw [principalLevelFrame.conjT_S, principalLevelFrame.conjT_S, principalLevelFrame.conjSub_conjSub]
    exact Formalism.L2.NG.IsoRep.refl _
  have hspan : (⨆ π, principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)) = Mult.goodPart R.θ (R.MY 0) J χ R.e0 := by
    refine le_antisymm (iSup_le fun π => inf_le_left) ?_
    rw [← key.1]
    refine iSup_le fun ρ => ?_
    by_cases h0 : principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ = ⊥
    · rw [h0]
      exact bot_le
    · have he1 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.FinTyp.conjT ρ) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ :=
        principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (hcc ρ)
      have hocc : principalLevelFrame.FinTyp.conjT ρ ∈ y.occ F.lv2 := ⟨b, by rw [he1]; exact h0⟩
      obtain ⟨π, hπ⟩ := hR.all _ hocc
      have he2 : principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π) = principalLevelFrame.isotL R.θ y.PY (R.MY 0) J χ R.e0 ρ := by
        rw [← he1]
        exact principalLevelFrame.isotL_iso R.θ y.PY (R.MY 0) J χ R.e0 (principalLevelFrame.conjT_iso hπ)
      exact le_iSup_of_le π (le_of_eq he2.symm)
  refine ⟨?_, ?_⟩
  · unfold Hd.prtE
    show (⨆ π, (principalLevelFrame.isotE R.θ y.PY (R.MY 0) J χ R.e0 (rep π)).map
        (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap) =
      (Mult.goodPart R.θ (R.MY 0) J χ R.e0).map (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap
    rw [← hspan, Submodule.map_iSup]
  · intro π π' hne x hx x' hx'
    obtain ⟨u, hu, rfl⟩ := hx
    obtain ⟨u', hu', rfl⟩ := hx'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (rep π)).Iso (principalLevelFrame.FinTyp.conjT (rep π')) :=
      principalLevelFrame.not_iso_conjT fun h => hne (hR.inj π π' h)
    have := key.2 _ _ hni u hu u' hu'
    show ipMT (R.MY 0) (ENNReal.ofReal (RealDat.nP F.lv2 b)⁻¹ • R.ν0) R.fd0 _ _ = 0
    unfold ipMT
    convert this using 2 <;> exact LinearEquiv.symm_apply_apply _ _

end GlobalTheory.Mem.R3.Rw.TypesRows
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypePartsSpanAndOrthogonalStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.rowFiniteTypeParts_span_and_orthogonal : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ b : Bool, (⨆ π, y.prtE F.lv2 b (rep π)) = (y.C F.lv2).EEc b ∧ ∀ π π', π ≠ π' → ∀ x ∈ y.prtE F.lv2 b (rep π), ∀ x' ∈ y.prtE F.lv2 b (rep π'), (y.C F.lv2).ipE b x x' = 0 := by
  first | exact @GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth | exact GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth | (intros; apply GlobalTheory.Mem.R3.Rw.TypesRows.parts_span_orth <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopSpacesMapOntoChainTopInCoordinates

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

noncomputable section
namespace GlobalTheory.TopRead

section Gen
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def constrOf (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W) : V →ₗ[ℂ] W :=
  (Module.Basis.mk hli hsp.ge).constr ℂ (fun k => a (Pi.single k 1))

theorem single_decomp (x : Fin n → K) : x = ∑ k, x k • (Pi.single k 1 : Fin n → K) := by
  ext i; simp [Finset.sum_apply, Pi.single_apply]

theorem semi_decomp {U : Type} [AddCommGroup U] [Module ℂ U] (f : (Fin n → K) →ₛₗ[σ] U) (x : Fin n → K) :
    f x = ∑ k, σ (x k) • f (Pi.single k 1) := by
  conv_lhs => rw [single_decomp x]

  simp only [map_sum, LinearMap.map_smulₛₗ]

theorem constrOf_apply (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W) (x : Fin n → K) :
    constrOf σ j hli hsp a (j x) = a x := by

  rw [semi_decomp σ j x, semi_decomp σ a x, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul]
  unfold constrOf
  congr 1
  have : j (Pi.single k 1) = Module.Basis.mk hli hsp.ge k := (Module.Basis.mk_apply hli hsp.ge k).symm
  rw [this, Module.Basis.constr_basis]

theorem constrOf_range (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W) :
    LinearMap.range (constrOf σ j hli hsp a) = Submodule.span ℂ (Set.range a) := by
  unfold constrOf
  rw [Module.Basis.constr_range]
  apply le_antisymm
  · exact Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    rw [semi_decomp σ a x]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Gen
end GlobalTheory.TopRead

namespace GlobalTheory.TopRead
section Iso
variable {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {W : Type} [AddCommGroup W] [Module ℂ W]

theorem constrOf_props (j : (Fin n → K) →ₛₗ[σ] V) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (a : (Fin n → K) →ₛₗ[σ] W)
    (S C : Submodule ℂ W) (ip : W → W → ℂ) (hC : PeterssonHilbertSpace.IsHermPos C ip) (hSC : S ≤ C)
    (hspan : Submodule.span ℂ (Set.range a) = S) (hip : ∀ x y, ip (a x) (a y) = inner ℂ (j x) (j y)) :
    Function.Injective (constrOf σ j hli hsp a) ∧ LinearMap.range (constrOf σ j hli hsp a) = S ∧
      ∀ v v', inner ℂ v v' = ip (constrOf σ j hli hsp a v) (constrOf σ j hli hsp a v') := by
  set J := constrOf σ j hli hsp a with hJ
  have hR : LinearMap.range J = S := by rw [hJ, constrOf_range, hspan]
  have mem : ∀ v, J v ∈ C := fun v => hSC (hR ▸ LinearMap.mem_range_self J v)
  have add1 : ∀ v₁ v₂ v', ip (J (v₁ + v₂)) (J v') = ip (J v₁) (J v') + ip (J v₂) (J v') := fun v₁ v₂ v' => by
    rw [map_add (f := _)]; exact hC.add ⟨_, mem v₁⟩ ⟨_, mem v₂⟩ ⟨_, mem v'⟩
  have smul1 : ∀ (c : ℂ) v v', ip (J (c • v)) (J v') = starRingEnd ℂ c * ip (J v) (J v') := fun c v v' => by
    rw [map_smul]; exact hC.smul c ⟨_, mem v⟩ ⟨_, mem v'⟩
  have herm : ∀ v v', ip (J v) (J v') = starRingEnd ℂ (ip (J v') (J v)) := fun v v' =>
    (hC.herm ⟨_, mem v'⟩ ⟨_, mem v⟩).symm
  have add2 : ∀ v v₁ v₂, ip (J v) (J (v₁ + v₂)) = ip (J v) (J v₁) + ip (J v) (J v₂) := fun v v₁ v₂ => by
    rw [herm, add1, map_add (f := _), ← herm, ← herm]
  have smul2 : ∀ (c : ℂ) v v', ip (J v) (J (c • v')) = c * ip (J v) (J v') := fun c v v' => by
    rw [herm, smul1, map_mul, Complex.conj_conj, ← herm]
  let B : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun v v' => ip (J v) (J v'))
    add1 smul1 add2 smul2
  let bas := Module.Basis.mk hli hsp.ge
  have hB : innerₛₗ ℂ = B := by
    refine LinearMap.ext_basis bas bas fun k l => ?_
    simp only [B, LinearMap.mk₂'ₛₗ_apply, bas, Module.Basis.mk_apply, hJ, constrOf_apply, hip]
    rfl
  have hI : ∀ v v', inner ℂ v v' = ip (J v) (J v') := fun v v' => by
    have := congrArg (fun f => f v v') hB
    simpa [B] using this
  refine ⟨fun v v' h => ?_, hR, hI⟩
  have h0 : ip 0 0 = 0 := by
    have := hC.smul 0 ⟨0, C.zero_mem⟩ ⟨0, C.zero_mem⟩
    simpa using this
  have : inner ℂ (v - v') (v - v') = (0 : ℂ) := by
    rw [hI, map_sub, h, sub_self, h0]
  exact sub_eq_zero.1 (inner_self_eq_zero.1 this)

end Iso
end GlobalTheory.TopRead

namespace GlobalTheory.TopRead



theorem top_read : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ jX : ∀ μ, (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX, (∀ μ, y.Us μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ (jX μ x) (jX μ x')) ∧ ∀ t, y.Us (y.tup t) → ∀ x, jX (y.tup t) (((tA (y.tup t)).cast (hA t)).j x) = R.toRealDat.cX.toMap R.toRealDat.prX ((R.toRealDat.HX t).e (R.toRealDat.jX t (rowForm A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t x))) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y b m s tA hA
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have hT := GlobalTheory.T.classSums_eq_pairings_topChain_lifts D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hB hP.keep.prX hH.ok.ok2
  have hHil := GlobalTheory.HilbertLevels.spaces_hilbert D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hI hB
  let aS : ∀ t, (Fin (rDim D A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) → D.what₂.LL) →ₛₗ[D.what₂.embLL] (y.C F.lv2).AmbX := fun t =>
    ((R.toRealDat.cX.toMap R.toRealDat.prX).comp (R.toRealDat.HX t).e).comp
      ((R.toRealDat.jX t).comp (((A3.A.fam.R t).S.basis.equivFun.symm.toLinearMap).comp
        ((A3.A.fam.R t).S.lvlE (A3.A.fam.R t).r (A3.A.fam.lvl (levP F.lv2 b).1 (levP F.lv2 b).2).P
          (A3.A.fam.lvl (levP F.lv2 b).1 (levP F.lv2 b).2).ψ).mulVecLin))
  have haS : ∀ t x, aS t x = R.toRealDat.cX.toMap R.toRealDat.prX ((R.toRealDat.HX t).e (R.toRealDat.jX t
      (rowForm A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t x))) := fun t x => rfl
  let tie : ∀ t, Tie1 D.what₂.embLL (rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t) (s (y.tup t)) := fun t => (tA (y.tup t)).cast (hA t)
  let J' : ∀ t, (s (y.tup t)).A.T →ₗ[ℂ] (y.C F.lv2).AmbX := fun t =>
    constrOf D.what₂.embLL (tie t).j (tie t).forms.li (tie t).forms.span (aS t)
  classical
  let jX : ∀ μ, (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX := fun μ =>
    if h : y.tup (y.tupT μ) = μ then (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) (J' (y.tupT μ)) : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) else 0
  have hcast : ∀ t₁ t₂ (e : t₁ = t₂) (h : y.tup t₁ = y.tup t₂), (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) (J' t₁) : (s (y.tup t₂)).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) = J' t₂ := by
    intro t₁ t₂ e h; subst e; rfl
  have hused : ∀ μ, y.Us μ → y.tup (y.tupT μ) = μ := by
    rintro μ (rfl | ⟨w, rfl⟩)
    · rw [← y.tup0, y.tupT_tup]
    · rw [y.tupT_tup]
  have hTb : ∀ μ, Submodule.span ℂ (Set.range (aS (y.tupT μ))) = (y.C F.lv2).CCXP b μ ∧ ∀ x x',
      (y.C F.lv2).ipXP b μ (aS (y.tupT μ) x) (aS (y.tupT μ) x') =
        D.what₂.embLL (Formalism.DivisionValues.hform (rH D A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 (y.tupT μ)) x x') := by
    intro μ
    cases b
    · exact (hT μ).2.1
    · exact (hT μ).1
  clear_value aS
  clear hT
  refine ⟨jX, fun μ hμ => ?_, fun t ht x => ?_⟩
  · have key : ∀ ν (h : ν = μ) (L : (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX), (Function.Injective L ∧ LinearMap.range L = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ (L x) (L x')) → (Function.Injective (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) ∧ LinearMap.range (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ ((cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) x) ((cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) h) L : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) x')) := by
      intro ν h L hL; subst h; exact hL
    have e : jX μ = (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) (hused μ hμ)) (J' (y.tupT μ)) : (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) := dif_pos (hused μ hμ)
    rw [e]
    refine key _ (hused μ hμ) (J' (y.tupT μ)) ?_
    have hHb := (hHil.1 b).2 μ
    exact constrOf_props D.what₂.embLL _ _ _ (aS (y.tupT μ)) _ _ _ hHb.2.2.1 hHb.2.1 (hTb μ).1 fun x x' => by
      rw [(hTb μ).2]
      exact ((tie (y.tupT μ)).forms.inner x x').symm
  · show jX (y.tup t) ((tie t).j x) = _
    have e : jX (y.tup t) = (cast (congrArg (fun ν => (s ν).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) (hused _ ht)) (J' (y.tupT (y.tup t))) : (s (y.tup t)).A.T →ₗ[ℂ] (y.C F.lv2).AmbX) := dif_pos (hused _ ht)
    rw [e, hcast _ _ (y.tupT_tup t) (hused _ ht)]
    exact (constrOf_apply D.what₂.embLL (tie t).j (tie t).forms.li (tie t).forms.span (aS t) x).trans (haS t x)

end GlobalTheory.TopRead
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopSpacesMapOntoChainTopInCoordinatesStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

theorem _root_.GlobalTheory.T.topSpaces_map_onto_chainTop_in_coordinates : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ jX : ∀ μ, (s μ).A.T →ₗ[ℂ] (y.C F.lv2).AmbX, (∀ μ, y.Us μ → Function.Injective (jX μ) ∧ LinearMap.range (jX μ) = (y.C F.lv2).CCXP b μ ∧ ∀ x x', ⟪x, x'⟫_ℂ = (y.C F.lv2).ipXP b μ (jX μ x) (jX μ x')) ∧ ∀ t, y.Us (y.tup t) → ∀ x, jX (y.tup t) (((tA (y.tup t)).cast (hA t)).j x) = R.toRealDat.cX.toMap R.toRealDat.prX ((R.toRealDat.HX t).e (R.toRealDat.jX t (rowForm A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t x))) := by
  first | exact @GlobalTheory.TopRead.top_read | exact GlobalTheory.TopRead.top_read | (intros; apply GlobalTheory.TopRead.top_read <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpaces

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw.ChainLevel



theorem chain_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG hI hP hH y Φ rep hR b m s tA hA
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  obtain ⟨h1, h2, -⟩ := GlobalTheory.HilbertLevels.spaces_hilbert D G Pl0 T A3.A Ks R.toRealDat F.lv2 y.tupT y.hm y.hTop y.hinj hI hB
  obtain ⟨jX, hjX, htop⟩ := GlobalTheory.T.topSpaces_map_onto_chainTop_in_coordinates D G Pl0 I0 T A3 Ks R F cG hI hP hH y b m s tA hA
  obtain ⟨EE, Mult, mZ, mT, io, jE, jM, hEi, hEr, hEip, hM, hio0, hio, hioT, hjunk⟩ :=
    GlobalTheory.T.exists_hilbertChain_of_level_over_tops D (y.C F.lv2) b y.Us (fun μ => (s μ).A) jX D.R.two_le_m (h1 b).1 (h1 b).2 (h2 b) hjX
  obtain ⟨hsup, horth⟩ := GlobalTheory.T.rowFiniteTypeParts_span_and_orthogonal D G Pl0 I0 T A3 Ks R F cG hI hP hH y Φ rep hR b
  classical
  haveI : Finite Φ := hR.fin
  haveI : Fintype Φ := Fintype.ofFinite Φ
  have hle : ∀ π, y.prtE F.lv2 b (rep π) ≤ LinearMap.range jE := fun π => hEr ▸ hsup ▸ le_iSup (fun π => y.prtE F.lv2 b (rep π)) π
  let p : Φ → Submodule ℂ EE.T := fun π => (y.prtE F.lv2 b (rep π)).comap jE
  have hmap : ∀ π, (p π).map jE = y.prtE F.lv2 b (rep π) := fun π => Submodule.map_comap_eq_of_le (hle π)
  have hptop : (⨆ π, p π) = ⊤ := by
    apply Submodule.map_injective_of_injective hEi
    rw [Submodule.map_iSup, Submodule.map_top, hEr]
    simp only [hmap]
    exact hsup
  have hporth : ∀ π π', π ≠ π' → p π ⟂ p π' := by
    intro π π' hne
    rw [Submodule.isOrtho_iff_inner_eq]
    intro u hu v hv
    rw [hEip]
    exact horth π π' hne _ hu _ hv
  obtain ⟨bs, ty, hft⟩ := GlobalTheory.Mem.exists_orthonormalBasis_adapted EE.T Φ p hptop hporth
  have hdisj : ∀ π π', π ≠ π' → y.prtE F.lv2 b (rep π) ⊓ y.prtE F.lv2 b (rep π') = ⊥ := by
    intro π π' hne
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.1 hx
    have hxE : x ∈ (y.C F.lv2).EEc b := hEr ▸ hle π hx1
    have h0 := horth π π' hne x hx1 x hx2
    by_contra hne0
    have := (h1 b).1.pos ⟨x, hxE⟩ (fun h => hne0 (by simpa using congrArg Subtype.val h))
    rw [h0] at this
    simp at this
  exact ⟨⟨EE, Mult, mZ, mT, io, _, bs, ty⟩, ⟨jE, jM, jX, hEi, hEr, hEip, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).1,
    fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.1, fun μ hμ j hj1 hj2 => (hM μ hμ j hj1 hj2).2.2,
    fun μ hμ => (hjX μ hμ).1, fun μ hμ => (hjX μ hμ).2.1, fun μ hμ => (hjX μ hμ).2.2, hio0, hio, hioT, hjunk,
    hft, hdisj, htop⟩⟩

end GlobalTheory.Mem.R3.Rw.ChainLevel
end
end
