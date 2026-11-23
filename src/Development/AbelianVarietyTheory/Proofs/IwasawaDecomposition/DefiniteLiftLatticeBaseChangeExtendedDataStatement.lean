module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBaseEnlargementFixedCoefFieldOfCoeffEnlargemen
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Forms
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockBaseChangeAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDataLevelFormsTransportFieldMap
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.WittVector.IsPoly
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendedDataLiftBlockDatumBaseChangeOneMatrix

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatible

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.R3.LiftLatBC

open Module NumberField Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.Mem.R3.DefLatBC
open scoped Matrix

theorem tl_bcF_of_blockBCAt : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  intro K K' _ _ _ _ _ _ G G' _ _ _ _ Pl0 Pl0' φ hφ e B B' ℓ ℓ' Z Z' s C _ h
  obtain ⟨hC, hH, hact, hnab, hZ, hX, hP, hψ⟩ := h
  obtain ⟨X', P', ψ'⟩ := ℓ'
  dsimp only at hX hP hψ
  subst hP
  obtain ⟨m, b, F, hF, hI, hb⟩ := exists_dual_family φ
  have hc : Nat.card (ℓ.P.map e.toMonoidHom) = Nat.card ℓ.P :=
    (Nat.card_congr (ℓ.P.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  have hl := lvlIdem_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.P ℓ.ψ ψ' hψ
  have hg : B'.S.gaMat B'.r (goodAt X' (ℓ.P.map e.toMonoidHom) ψ') * C = C * (B.S.gaMat B.r (goodAt ℓ.X ℓ.P ℓ.ψ)).map φ := by
    unfold goodAt
    rw [(group_action_matrix_hom K' B'.S G' B'.r).2, (group_action_matrix_hom K B.S G B.r).2, Matrix.mul_assoc, hl, ← Matrix.mul_assoc,
      idemOf_baseChange φ e B.S B.r B'.S B'.r C hact ℓ.X X' hX, Matrix.map_mul, Matrix.mul_assoc]
  set ℓ' : Lvl K' G' := ⟨X', ℓ.P.map e.toMonoidHom, ψ'⟩ with hℓ'
  obtain ⟨A0, hA0, hE0⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hl)
  obtain ⟨A1, hA1, hE1⟩ := subE_baseChange φ C hC.1 _ _ (range_baseChange φ C hC.2 C _ _ hg)
  change B'.S.lvlE B'.r ℓ'.P ℓ'.ψ * A0 = C * (B.S.lvlE B.r ℓ.P ℓ.ψ).map φ at hE0
  change B'.vE ℓ' * A1 = C * (B.vE ℓ).map φ at hE1
  have hZ0 : B'.Z0 ℓ' Z' = Submodule.span K' ((fun x : Fin (B.nV ℓ) → K => A1 *ᵥ (fun k => φ (x k))) '' (B.Z0 ℓ Z : Set _)) :=
    comap_baseChange (R := K) (R' := K') φ (fun i => algebraMap (𝓞 K') K' (b i)) F hF (fun i a => ⟨F i a, rfl⟩) hb
      C hC.1 A1 hA1.2 _ _ hE1 _ _ hZ _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  obtain ⟨Gm, hGm, hE2⟩ := subE_baseChange φ A1 hA1.1 _ _ hZ0
  change B'.zE ℓ' Z' * Gm = A1 * (B.zE ℓ Z).map φ at hE2
  have hvPr : B'.vPr ℓ' * C = A1 * (B.vPr ℓ).map φ := orthPr_baseChange φ hφ C A1 hA1 _ _ hH _ _ hE1
  have hHV : A1ᴴ * B'.HV ℓ' * A1 = (B.HV ℓ).map φ := by
    have h1 := gram_baseChange φ hφ C A1 _ _ hH _ _ hE1
    change A1ᴴ * ((Nat.card (ℓ.P.map e.toMonoidHom) : K')⁻¹ • ((B'.vE ℓ')ᴴ * B'.S.H * B'.vE ℓ')) * A1 =
      ((Nat.card ℓ.P : K)⁻¹ • ((B.vE ℓ)ᴴ * B.S.H * B.vE ℓ)).map φ
    rw [Matrix.mul_smul, Matrix.smul_mul, h1, hc]
    generalize (B.vE ℓ)ᴴ * B.S.H * B.vE ℓ = M
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast]
  have hPq : B'.Pq ℓ' Z' * A1 = Gm * (B.Pq ℓ Z).map φ := orthPr_baseChange φ hφ A1 Gm hGm _ _ hHV _ _ hE2
  have hlPr : B'.lPr ℓ' Z' * A0 = Gm * (B.lPr ℓ Z).map φ := by
    unfold BlockDat.lPr
    rw [Matrix.mul_assoc, hE0, Matrix.mul_assoc, ← Matrix.mul_assoc (B'.vPr ℓ'), hvPr, Matrix.mul_assoc A1,
      ← Matrix.mul_assoc (B'.Pq ℓ' Z'), hPq, Matrix.map_mul, Matrix.map_mul]
    simp only [Matrix.mul_assoc]
  have hN : B'.S.lvlNab B'.r ℓ'.P ℓ'.ψ = Submodule.span (𝓞 K')
      ((fun x : Fin (B.S.lvlDim B.r ℓ.P ℓ.ψ) → K => A0 *ᵥ (fun k => φ (x k))) '' (B.S.lvlNab B.r ℓ.P ℓ.ψ : Set _)) :=
    comap_baseChange (R := 𝓞 K) (R' := 𝓞 K') φ b F hF hI hb
      C hC.1 A0 hA0.2 _ _ hE0 _ _ hnab _ _ (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  refine ⟨Gm, hGm, ?_, fun x => ?_⟩
  · unfold BlockDat.Tl matLat
    rw [hN]
    exact map_baseChange φ A0 Gm _ _ hlPr _
  · have hv : B'.vE ℓ' *ᵥ (B'.zE ℓ' Z' *ᵥ (Gm *ᵥ fun k => φ (x k))) =
        C *ᵥ fun k => φ ((B.vE ℓ *ᵥ (B.zE ℓ Z *ᵥ x)) k) := by
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc, hE2, ← Matrix.mul_assoc, hE1,
        Matrix.mul_assoc, ← Matrix.map_mul, ← Matrix.mulVec_mulVec, map_mulVec', ← Matrix.mulVec_mulVec]
    simp only [BlockDat.toF, bcF, LinearMap.coe_comp, Function.comp_apply, Matrix.mulVecLin_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    rw [hv]

end GlobalTheory.Mem.R3.LiftLatBC

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockDatumBaseChangeDefiniteLatticeCompatibleStatement

section

@[expose] public section

open NumberField
open scoped Matrix

theorem _root_.GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible : ∀ {K K' : Type} [Field K] [NumberField K] [StarRing K] [Field K'] [NumberField K'] [StarRing K']
  {G G' : Type} [Group G] [Fintype G] [Group G'] [Fintype G'] {Pl0 Pl0' : Type}
  (φ : K →+* K'), (∀ x : K, φ (star x) = star (φ x)) → ∀ (e : G ≃* G') (B : Formalism.L2.DIV.BlockDat K G Pl0) (B' : Formalism.L2.DIV.BlockDat K' G' Pl0')
    (ℓ : Formalism.L2.DIV.Lvl K G) (ℓ' : Formalism.L2.DIV.Lvl K' G') (Z : Submodule K B.S.Forms) (Z' : Submodule K' B'.S.Forms) (s : ℕ)
    (C : Matrix (Fin B'.S.dim) (Fin B.S.dim) K'), B.Ok s → GlobalTheory.Mem.R3.LiftLatBC.BlockBaseChangeAt φ e B B' ℓ ℓ' Z Z' C →
    ∃ Gm : Matrix (Fin (B'.dZ ℓ' Z')) (Fin (B.dZ ℓ Z)) K', Function.Bijective Gm.mulVec ∧
      B'.Tl ℓ' Z' = Submodule.span (𝓞 K') ((fun x : Fin (B.dZ ℓ Z) → K => Matrix.mulVec Gm (fun k => φ (x k))) '' (B.Tl ℓ Z : Set (Fin (B.dZ ℓ Z) → K))) ∧
      ∀ x : Fin (B.dZ ℓ Z) → K, B'.toF ℓ' Z' (Matrix.mulVec Gm fun k => φ (x k)) = GlobalTheory.Mem.R3.LiftLatBC.bcF φ B B' C (B.toF ℓ Z x) := by
  first | exact @GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | exact GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt | (intros; apply GlobalTheory.Mem.R3.LiftLatBC.tl_bcF_of_blockBCAt <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedData

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLatBC



theorem lift_lattice_bc : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ N : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective N.mulVec ∧
          (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec N fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).tC z'.F.cr false j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec N fun k => φ (x k)))) ((z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (GlobalTheory.T.extendedData_lift_blockDatum_baseChange_one_matrix h1 h2 h3 h4 h5 h6 h7) (StepW.of_all fun K B' f' T' w' _ _ hQ => ?_)
  intro B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  obtain ⟨e, C, hC, hθ⟩ := hQ B f T w hE hf hP hpx Z hX Wt z hG hGA hFine hL Z' hX' hG' hGA' hV z' hFine' hExt j j' hj φ hφ
  have hstar : ∀ x, φ (star x) = star (φ x) := fun x => (w'.st Z').toD7.what₂.embLL.injective (by
    rw [hφ, (w.st Z).toD7.starLL_cx, (w'.st Z').toD7.starLL_cx, hφ])
  obtain ⟨N, hN, hTl, hF⟩ := GlobalTheory.T.blockDatum_baseChange_definiteLattice_compatible φ hstar e _ _ _ _ _ _ 1 C (hL.ok.ok2.lifts j _) hC
  refine ⟨N, hN, hTl, fun x => ?_⟩
  refine HEq.trans (heq_of_eq (tC_cpt (z'.R.toCx3 z'.F) z'.F.cr false j' _ _)) (HEq.trans ?_ (heq_of_eq (tC_cpt (z.R.toCx3 z.F) z.F.cr false j _ x)).symm)
  have e1 : z'.F.cr.toL (z'.R.toCx3 z'.F).zs false j' _ (Matrix.mulVec N fun k => φ (x k)) =
      GlobalTheory.Mem.R3.LiftLatBC.bcF φ _ _ C (z.F.cr.toL (z.R.toCx3 z.F).zs false j _ x) := hF x
  exact HEq.trans (heq_of_eq (congrArg (fun y => (z'.R.toCx3 z'.F).θ' j' _ ((z'.R.toCx3 z'.F).jL j' _ y)) e1)) (hθ _)

end GlobalTheory.Mem.R3.LiftLatBC
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteLiftLatticeBaseChangeExtendedDataStatement

section

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem _root_.GlobalTheory.T.definiteLiftLattice_baseChange_extendedData : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ N : Matrix (Fin (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).dZ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0)) (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0)) (w'.st Z').toD7.what₂.LL, Function.Bijective N.mulVec ∧
          (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL => Matrix.mulVec N fun k => φ (x k)) '' ((((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Set (Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL))) ∧
          ∀ x : Fin (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).dZ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) → (w.st Z).toD7.what₂.LL, HEq ((z'.R.toCx3 z'.F).tC z'.F.cr false j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.base3.v0.embedding (Matrix.mulVec N fun k => φ (x k)))) ((z.R.toCx3 z.F).tC z.F.cr false j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0 (Formalism.IndefR.Cx.cpt (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.base3.v0.embedding x))) := by
  first | exact @GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc | exact GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc | (intros; apply GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc <;> assumption)
end
end
