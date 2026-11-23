module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensional
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
public import Formalism.LocalToGlobal.Columns.CoefColLemmas
public import Formalism.LocalToGlobal.Columns.ColFormsLemmas
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Linter.Style
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasis
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawNormClassSumFockStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexForms
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondRepresentationStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalLatticeSpanAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbedding

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexFormsFiniteDimensionalStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.complexForms_finiteDimensional : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → FiniteDimensional ℂ (S.Fi emb σ lam) := by
  first | exact @GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | exact GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional | (intros; apply GlobalTheory.Mem.Col2.GStep.fi_finiteDimensional <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOk

section

@[expose] public section

noncomputable section

namespace GlobalTheory.Mem.Col2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms Matrix

section

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}


omit [NumberField K] [StarRing K] in
theorem GStep.lsh_eq_map (S : GStep E K n) (h : S.Ok) (b : S.β) (g : S.G b) (d : S.D b) :
    S.Lsh b (g • d) = (S.Lsh b d).map
      ((Matrix.mulVecLin (S.gam b g : Matrix (Fin n) (Fin n) E)).restrictScalars (𝓞 E)) := by
  ext y
  simp only [Submodule.mem_map, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply]
  have e : (S.gam b g : Matrix (Fin n) (Fin n) E) *ᵥ (((S.gam b g)⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ y = y := by
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  constructor
  · intro hy
    exact ⟨_, (h.lsh_smul b g d _).1 (by rw [e]; exact hy), e⟩
  · rintro ⟨x, hx, rfl⟩
    exact (h.lsh_smul b g d x).2 hx


omit [StarRing K] [Fintype ι] in
theorem GStep.tauLat_smul (S : GStep E K n) (h : S.Ok) (emb : ι → E →+* K) [Fintype ι] (b : S.β) (g : S.G b) (d : S.D b) (τ : ι) :
    tauLat emb τ (S.Lsh b (g • d)) = gLat (embGL emb (S.gam b g) τ) (tauLat emb τ (S.Lsh b d)) := by
  rw [S.lsh_eq_map h]
  exact tauLatG E K ι n emb τ _ (S.gam b g)

end

theorem fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι]
    {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n),
    FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF h b
  have hr : ∀ g : S.G b, ∃ m : ℕ, 0 < m ∧ ((S.chr b g : Kˣ) : K) ^ m = 1 := fun g => by
    obtain ⟨m, hm, hc⟩ := h.root b g
    exact ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]⟩
  refine ⟨h.fin_orb b, h.fin_stab b, ?_, ?_, ?_⟩
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show nabAtr emb lam (S.Lsh b (g • d)) = (nabAtr emb lam (S.Lsh b d)).map _
    unfold nabAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact nabK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g d
    obtain ⟨m, hm, hc⟩ := hr g
    refine Eq.trans ?_ (map_root_smul _ (rhoVr emb lam (S.gam b g)) hm hc).symm
    show delAtr emb lam (S.Lsh b (g • d)) = (delAtr emb lam (S.Lsh b d)).map _
    unfold delAtr
    simp_rw [S.tauLat_smul h emb b g d, dualFr_gLat]
    exact delK_gLat lam _ (invTrK (embGL emb (S.gam b g)))
  · intro g x y
    obtain ⟨m, hm, hc⟩ := hr g
    have hU : S.gam b g ∈ Formalism.UG.UJ (starRingEnd E) (1 : Matrix (Fin n) (Fin n) E) := by
      have := h.unit b g
      show _ * _ * _ = _
      rw [Matrix.mul_one]
      exact this
    have hi : pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (rhoVr emb lam (S.gam b g) x) (rhoVr emb lam (S.gam b g) y) =
        pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y :=
      pairInv K ι n lam _ _ (fun τ => (uJUnitary E K ι n emb (starRingEnd E) τ
        (fun x => (hF.emb_star τ x).symm) 1 _ hU).2 (by simp)) x y
    show pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) x)
      (((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) y) = pairVr emb lam (1 : Matrix (Fin n) (Fin n) E) x y
    rw [LinearMap.map_smulₛₗ₂, map_smul, hi, smul_smul]
    show (star ((S.chr b g : Kˣ) : K) * _) • _ = _
    rw [star_mul_root ⟨σ, hF.sig_star⟩ hm hc, one_smul]

end GlobalTheory.Mem.Col2

end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyFamOkStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_fam_ok : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → (S.fam emb lam).Ok := by
  first | exact @GlobalTheory.Mem.Col2.fam_ok | exact GlobalTheory.Mem.Col2.fam_ok | (intros; apply GlobalTheory.Mem.Col2.fam_ok <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianLatticeChartFamilyLawBasisStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.hermitianLatticeChartFamily_lawBasis : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawBasis emb σ lam h := by
  first | exact @GlobalTheory.Mem.Col2.lawBasis_all | exact GlobalTheory.Mem.Col2.lawBasis_all | (intros; apply GlobalTheory.Mem.Col2.lawBasis_all <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesComplexFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_complexForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → J.LawDiaStable emb σ hc := by
  first | exact @GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | exact GlobalTheory.Mem.Col2.DiaStab.lawDiaStable | (intros; apply GlobalTheory.Mem.Col2.DiaStab.lawDiaStable <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralForms

section

@[expose] public section

namespace GlobalTheory.Mem.Col2.DiaLat

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

section General

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem evV_rho_tr (b : S.β) (g : S.G b) (v : VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm

theorem exists_pull (hf : S.Free) (h : (S.fam emb lam).Ok) (p : ∀ c : S.Cl, S.D c.1)
    (hp : ∀ c, S.Lsh c.1 (p c) = S.Lsh c.1 (S.rep c)) (x : S.FormsK emb lam h) (hx : x ∈ (S.hlat emb lam h).L) :
    ∃ y ∈ (S.hlat emb lam h).L, ∀ c, S.embF emb σ lam h y c =
      S.trTo emb σ c.1 (p c) (S.embF emb σ lam h x (S.cl c.1 (p c))) := by
  refine ⟨⟨fun c => S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))), fun c g => ?_⟩, fun c => ?_, fun c => ?_⟩
  · have hg : (g.1 : S.G c.1) = 1 := hf c.1 g.1 (S.rep c) g.2
    show S.rho emb lam c.1 g.1 _ = _
    rw [hg, map_one]
    rfl
  · have h1 : delAtr emb lam (S.Lsh c.1 (S.mv c.1 (p c) • S.rep (S.cl c.1 (p c)))) =
        (delAtr emb lam (S.Lsh c.1 (S.rep (S.cl c.1 (p c))))).map
          ((S.rho emb lam c.1 (S.mv c.1 (p c))).restrictScalars (𝓞 K)) :=
      (h c.1).del_smul (S.mv c.1 (p c)) (S.rep (S.cl c.1 (p c)))
    rw [S.mv_smul, hp] at h1
    show S.rho emb lam c.1 (S.mv c.1 (p c)) (x.1 (S.cl c.1 (p c))) ∈ delAtr emb lam (S.Lsh c.1 (S.rep c))
    rw [h1]
    exact Submodule.mem_map_of_mem (hx (S.cl c.1 (p c)))
  · exact evV_rho_tr S emb σ lam c.1 _ _

end General

theorem dia_lat : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc _ _ hJ hF P a x hx
  obtain ⟨y, hy, e⟩ := exists_pull (I.S 0) emb σ (lamT hc 0) hJ.free0 hF (fun c => (J.A 0).diaPt P a c)
    (fun c => (hJ.lev 0).dia_Lsh c.1 P a _) x hx
  exact ⟨y, hy, funext e⟩

end GlobalTheory.Mem.Col2.DiaLat
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimeDiamondPreservesIntegralFormsStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.levelPrimeDiamond_preserves_integralForms : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (hF : ((I.S 0).fam emb (lamT hc 0)).Ok) P a x, x ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L → ∃ y ∈ ((I.S 0).hlat emb (lamT hc 0) hF).L, (I.S 0).embF emb σ (lamT hc 0) hF y = J.diaLin emb σ P a ((I.S 0).embF emb σ (lamT hc 0) hF x) := by
  first | exact @GlobalTheory.Mem.Col2.DiaLat.dia_lat | exact GlobalTheory.Mem.Col2.DiaLat.dia_lat | (intros; apply GlobalTheory.Mem.Col2.DiaLat.dia_lat <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightLawGoodOfFieldEmbeddingStatement

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

theorem _root_.GlobalTheory.T.weight_law_good_of_field_embedding : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact GlobalTheory.Mem.LatGood.lawGood S emb σ lam hF hS hS.lsh_full_lat h
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsAll

section

@[expose] public section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2



theorem laws_all : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {R : Ranks} (I : ChainIn E K ι R) (J : AtIn I) (emb : ι → E →+* K) (σ : K →+* ℂ) (hc : ι → HCParam R), FOk emb σ → ∀ (hI : I.Ok), J.Ok → ∀ (Q : PerIn I) (hQ : Q.Ok) (Pl : Rows.Places K), J.Laws emb σ hc ∧ FmLaws J Q emb σ hc Pl hI hQ := by
  intro E K ι _ _ _ _ _ _ _ R I J emb σ hc hF hI hJ Q hQ Pl
  have hd := GlobalTheory.T.levelPrimeDiamond_representation I J emb σ hc hF hI hJ
  have hfam : ∀ i, ((I.S i).fam emb (lamT hc i)).Ok := fun i => GlobalTheory.T.hermitianLatticeChartFamily_fam_ok (I.S i) emb σ (lamT hc i) hF (hI.step i)
  have hfamP : (Q.S'.fam emb Q.sgT).Ok := GlobalTheory.T.hermitianLatticeChartFamily_fam_ok Q.S' emb σ Q.sgT hF hQ.step
  refine ⟨⟨hd.1, hd.2, GlobalTheory.T.complexForms_finiteDimensional (I.S 0) emb σ (lamT hc 0) hF (hI.step 0), GlobalTheory.T.levelPrimeDiamond_preserves_complexForms I J emb σ hc hF hI hJ⟩, ?_⟩
  exact
    { fam := hfam
      famP := hfamP
      lev := fun i => GlobalTheory.T.tDat_laws_of_ok (J.A i) J.T (hI.step i) (hJ.lev i)
      good := fun i => GlobalTheory.T.weight_law_good_of_field_embedding (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      basis := fun i => GlobalTheory.T.hermitianLatticeChartFamily_lawBasis (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      norm := fun i => letI := I.clFin hI i; GlobalTheory.T.lawNorm_classSum_fock (I.S i) emb σ (lamT hc i) hF (hI.step i) _
      goodP := GlobalTheory.T.weight_law_good_of_field_embedding Q.S' emb σ Q.sgT hF hQ.step _
      basisP := GlobalTheory.T.hermitianLatticeChartFamily_lawBasis Q.S' emb σ Q.sgT hF hQ.step _
      normP := letI := Q.clFin hQ; GlobalTheory.T.lawNorm_classSum_fock Q.S' emb σ Q.sgT hF hQ.step _
      dia_lat := GlobalTheory.T.levelPrimeDiamond_preserves_integralForms I J emb σ hc hF hI hJ _
      B_span := fun i w P => GlobalTheory.T.local_lattice_span_at_place I J emb σ hc hF hI hJ Pl i _ w P }

end GlobalTheory.Mem.Col2
end
end
