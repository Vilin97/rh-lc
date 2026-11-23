module

public import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDeRhamFreeBaseChangeRigid
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleSpecProdAbelianCohomologousSumMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCocycleOnPointsIsCocycleAndEvalEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatFamilyExistsUnique
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.PiTensorProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointwiseCocycleOnCoverExtendsUpToCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtAlgCompRight
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangePullSumMulPointValueEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeBaseChangeSpecAlgebraProd
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCochainPullbackBaseChangeCocycleCoboundaryW

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCobWholeOfIsCobCover

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PtExt

theorem isCob_whole_of_isCob_cover : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (K : Type) (W : K → X.left.Opens), ⨆ i, W i = ⊤ → ∀ u : Fn1 X, IsCoc (whole X) u → ∀ k : Fn0 X, IsCob W u k → ∃ k' : Fn0 X, IsCob (whole X) u k' := by
  intro R _ X K W hW u hu k hk
  have ex : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D), ∃! d : D,
      ∀ (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), Sm W (D := E) (spOver ψ ≫ x) →
        k E (spOver ψ ≫ x) - u D E ψ x = ψ d := by
    intro D _ _ x
    refine natFamily_existsUnique R X K W hW D x (fun E _ _ ψ ↦ k E (spOver ψ ≫ x) - u D E ψ x) ?_
    intro E _ _ E' _ _ ψ θ hψ
    have c := hu D E E' ψ θ x (sm_whole x)
    have b := hk E E' θ (spOver ψ ≫ x) hψ
    have e : spOver (θ.comp ψ) ≫ x = spOver θ ≫ spOver ψ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    show k E' (spOver (θ.comp ψ) ≫ x) - u D E' (θ.comp ψ) x = θ (k E (spOver ψ ≫ x) - u D E ψ x)
    rw [e, c, b, map_sub]
    ring
  let k' : Fn0 X := fun D _ _ x ↦ (ex D x).exists.choose
  have hk' : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt X D) (E : Type) [CommRing E] [Algebra R E]
      (ψ : D →ₐ[R] E), Sm W (D := E) (spOver ψ ≫ x) → k E (spOver ψ ≫ x) - u D E ψ x = ψ (k' D x) :=
    fun D _ _ x ↦ (ex D x).exists.choose_spec
  refine ⟨k', fun D _ _ D' _ _ φ x _ ↦ ?_⟩
  have huniq : k' D' (spOver φ ≫ x) = u D D' φ x + φ (k' D x) := by
    refine (ex D' (spOver φ ≫ x)).unique (hk' D' (spOver φ ≫ x)) ?_
    intro E _ _ ψ hψ
    have e : spOver (ψ.comp φ) ≫ x = spOver ψ ≫ spOver φ ≫ x := by
      rw [← Category.assoc, spOver_comp]
    have h1 := hk' D x E (ψ.comp φ) (by rw [e]; exact hψ)
    have c := hu D D' E φ ψ x (sm_whole x)
    rw [e, c, AlgHom.comp_apply] at h1
    rw [map_add (f := _), ← h1]
    ring
  rw [huniq]
  ring

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParCocIsCoc

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem parCoc_isCoc : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) (K : Type) (W : K → (A ⊗ B).left.Opens) (J : Type) [Fintype J] (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → (∀ i, IsCoc (whole B) (b i)) → IsCupCob W a b n → ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsCoc (parCov W x) (parCoc a b n x) := by
  intro R _ A B K W J _ a b n ha hb hn D _ _ x
  unfold IsCoc at ha hb ⊢
  unfold IsCupCob at hn
  intro E _ _ E' _ _ E'' _ _ φ ψ z hz
  have hz' : Sm W (z ≫ x ▷ B) := by
    unfold Sm at hz ⊢
    obtain ⟨k, hk⟩ := hz
    refine ⟨k, ?_⟩
    simpa [parCov, Over.comp_left, Scheme.Hom.comp_preimage] using hk
  have h1 := hn E E' E'' φ ψ (z ≫ x ▷ B) hz'
  have hfst : (z ≫ x ▷ B) ≫ fst _ _ = spOver (ptAlg (z ≫ fst _ _)) ≫ x := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc, spOver_ptAlg]
  have hα : ptAlg ((spOver φ ≫ z) ≫ fst _ _) = φ.comp (ptAlg (z ≫ fst _ _)) := by
    rw [Category.assoc, ptAlg_comp]
  have ha' := fun i ↦ ha i D E E' (ptAlg (z ≫ fst _ _)) φ x (sm_whole _)
  have hb' := fun i ↦ hb i E E' E'' φ ψ (z ≫ snd _ _) (sm_whole _)
  rw [hfst] at h1
  simp only [Category.assoc, whiskerRight_snd] at h1
  simp only [parCoc]
  rw [hα]
  simp only [ha', hb', Category.assoc]

  simp only [map_sub, map_sum, map_mul, map_add (f := _), AlgHom.comp_apply, add_mul, mul_add, Finset.sum_add_distrib]
  linear_combination -h1

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParCocSpOver

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem parCoc_spOver (R : Type) [CommRing R] (A B : Over (Sp R)) (J : Type) [Fintype J]
    (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (ha : ∀ i, IsCoc (whole A) (a i))
    (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D']
    (φ : D →ₐ[R] D') (x : Pt A D) :
    parCoc (D := D') a b n (spOver φ ≫ x) =
      ((parCoc (D := D) a b n x).pull (spOver φ ▷ B)).add
        (sumMul (D := D') (fun i ↦ a i D D' φ x) b) := by
  funext E _ _ E' _ _ ψ z
  simp only [parCoc, Fn1.pull, Fn1.add, sumMul]
  have h1 : z ≫ (spOver φ ≫ x) ▷ B = (z ≫ spOver φ ▷ B) ≫ x ▷ B := by
    rw [comp_whiskerRight, Category.assoc]
  have h2 : (z ≫ spOver φ ▷ B) ≫ snd _ _ = z ≫ snd _ _ := by
    rw [Category.assoc, whiskerRight_snd]
  have h3 : ptAlg ((z ≫ spOver φ ▷ B) ≫ fst _ _) =
      (ptAlg (z ≫ fst (SpAlg R D') B)).comp φ := by
    rw [Category.assoc, whiskerRight_fst, ← Category.assoc]
    conv_lhs => rw [← spOver_ptAlg (z ≫ fst (SpAlg R D') B)]
    rw [spOver_comp, ptAlg_spOver]
  rw [h1, h2, h3]
  have hc : ∀ i, a i D E ((ptAlg (z ≫ fst _ _)).comp φ) x =
      ptAlg (z ≫ fst _ _) (a i D D' φ x) + a i D' E (ptAlg (z ≫ fst _ _)) (spOver φ ≫ x) :=
    fun i ↦ ha i D D' E φ _ x (sm_whole x)
  simp only [hc, map_add (f := _), add_mul, Finset.sum_add_distrib]
  ring

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulHodgeFilEqZeroOfDeRhamCoboundary

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem sum_mul_eq_zero_of_isCob : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ y ∈ Fil B, ∀ (D : Type) [CommRing D] [Algebra R D] (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B), (∃ k, IsCob (whole _) (sumMul d fun i ↦ fv (β i)) k) → ∑ i, d i * algebraMap R D (y ⟨_, hβ i⟩) = 0 := by
  intro H R _ B _ g hB hg y hy D _ _ J _ d β hβ hcob
  obtain ⟨-, -, hBC⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange H
  obtain ⟨B', _, π, q, hpb, -, -, -, hq1, hq2⟩ :=
    GlobalTheory.exists_baseChange_spAlg_prod R D B g hB hg
  have w : q ≫ (SpAlg R D ⊗ B).hom = B'.hom ≫ spMap (algebraMap R D) := by
    rw [← Over.w (snd (SpAlg R D) B), ← Category.assoc, hq2]
    exact hpb.1.w
  let m := GlobalTheory.Published.AbelianDeRham.bcMor hpb
  obtain ⟨hm, hspan⟩ := hBC R B g hB hg D B' π hpb
  obtain ⟨y', hy'⟩ := hm.exists y

  have hFil : ∀ c ∈ PrimitiveSubmodule B', y' c = 0 := by
    intro c hc
    rw [hspan] at hc
    refine Submodule.span_induction (p := fun c _ ↦ y' c = 0) ?_ (by simp) (fun a b _ _ ha hb ↦ by simp [ha, hb])
      (fun r a _ ha ↦ by simp [ha]) hc
    rintro _ ⟨c, hc, rfl⟩
    rw [hy' c, (Submodule.mem_dualAnnihilator _).1 hy c hc, map_zero]

  obtain ⟨k, hk⟩ := (GlobalTheory.PtExt.bcPull_keeps R D (algebraMap R D) (SpAlg R D ⊗ B) B' q w _).2 hcob
  rw [GlobalTheory.PtExt.bcPull_sumMul_fv R D B B' q w π hq1 hq2 m.isMor J d β] at hk
  have hF1 := (mem_hodgeFiltration_iff_pointwiseCoboundary D B' _).2 ⟨k, hk⟩
  let c' : primDR B' := ∑ i, d i • m.pull ⟨_, hβ i⟩
  have hc' : (c' : FirstDeRham (B'.hom ≫ 𝟙 _)) = CatCoh.H1.mk _ (∑ i, d i • m.isMor.coef.pullbackOneCocycle (β i)) := by

    simp only [c', Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
    rfl
  have h0 : y' c' = 0 := hFil c' (Submodule.mem_comap.2 (by rw [Submodule.subtype_apply, hc']; exact hF1))
  rw [← h0]

  simp only [c', map_sum, map_smul, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ ↦ by rw [hy' _]

end GlobalTheory.PtExt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumMulHodgeFilEqZeroOfDeRhamCoboundaryStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.sum_mul_hodgeFil_eq_zero_of_deRham_coboundary : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ y ∈ Fil B, ∀ (D : Type) [CommRing D] [Algebra R D] (J : Type) [Fintype J] (d : J → D) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B), (∃ k, IsCob (whole _) (sumMul d fun i ↦ fv (β i)) k) → ∑ i, d i * algebraMap R D (y ⟨_, hβ i⟩) = 0 := by
  first | exact @GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob | exact GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob | (intros; apply GlobalTheory.PtExt.sum_mul_eq_zero_of_isCob <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundaryOfMemHodgeFiltration

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.OrthPt

variable {R : Type} [CommRing R]

theorem iSup_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens} (hW : ⨆ i, W i = ⊤)
    {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) : ⨆ i, parCov W x i = ⊤ := by
  unfold parCov
  exact (x ▷ B).left.iSup_preimage_eq_top hW

theorem sm_parCov {A B : Over (Sp R)} {K : Type} {W : K → (A ⊗ B).left.Opens}
    {D D' E : Type} [CommRing D] [Algebra R D] [CommRing D'] [Algebra R D'] [CommRing E] [Algebra R E]
    (φ : D →ₐ[R] D') (x : Pt A D) (z : Pt (SpAlg R D' ⊗ B) E) (h : Sm (parCov W (spOver φ ≫ x)) z) :
    Sm (parCov W x) (z ≫ spOver φ ▷ B) := by
  obtain ⟨i, hi⟩ := h
  refine ⟨i, ?_⟩
  unfold parCov at hi ⊢
  rw [comp_whiskerRight, Over.comp_left, Scheme.Hom.comp_preimage] at hi
  rw [Over.comp_left, Scheme.Hom.comp_preimage]
  exact hi

theorem sumMul_elim {B : Over (Sp R)} {D : Type} [CommRing D] [Algebra R D] {I₁ I₂ I₃ : Type} [Fintype I₁]
    [Fintype I₂] [Fintype I₃] (d₁ : I₁ → D) (d₂ : I₂ → D) (d₃ : I₃ → D)
    (β₁ : I₁ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (β₂ : I₂ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (β₃ : I₃ → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))
    (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E')
    (z : Pt (SpAlg R D ⊗ B) E) :
    sumMul (Sum.elim d₁ (Sum.elim (fun i ↦ -d₂ i) (fun i ↦ -d₃ i)))
        (fun i ↦ fv (Sum.elim β₁ (Sum.elim β₂ β₃) i)) E E' ψ z =
      sumMul d₁ (fun i ↦ fv (β₁ i)) E E' ψ z - sumMul d₂ (fun i ↦ fv (β₂ i)) E E' ψ z -
        sumMul d₃ (fun i ↦ fv (β₃ i)) E E' ψ z := by
  simp only [sumMul, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, map_neg, neg_mul, Finset.sum_neg_distrib]
  ring

theorem exists_isCob_of_mem_fil : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → ∀ (K : Type) (W : K → (A ⊗ B).left.Opens), ⨆ i, W i = ⊤ → ∀ (J : Type) [Fintype J] (a : J → Fn1 A) (β : J → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (hβ : ∀ i, CatCoh.H1.mk _ (β i) ∈ primDR B) (n : Fn1 (A ⊗ B)), (∀ i, IsCoc (whole A) (a i)) → IsCupCob W a (fun i ↦ fv (β i)) n → ∀ y ∈ Fil B, ∃ k : Fn0 A, IsCob (whole A) (fun D _ _ D' _ _ φ x ↦ ∑ i, a i D D' φ x * algebraMap R D' (y ⟨_, hβ i⟩)) k := by
  intro H R _ A B _ g hB hg K W hW J _ a β hβ n ha hn y hy
  have hP : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f ∈ primDR B := fun f ↦ by
    have h : primDR B = ⊤ := ((GlobalTheory.abelianDeRham_free_baseChange_rigid H).1 R B g hB hg).1
    rw [h]; trivial
  have hfv : ∀ f : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)), IsCoc (whole B) (fv f) := fun f ↦ (fv_isCoc_and_ev_eq R B f).1
  have key : ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      ∃ (m : ℕ) (d : Fin m → D) (c : Fin m → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) (k : Fn0 (SpAlg R D ⊗ B)),
        IsCob (parCov W x) ((parCoc a (fun i ↦ fv (β i)) n x).add (sumMul d fun i ↦ fv (c i)).neg) k := by
    intro D _ _ x
    obtain ⟨u, hu, k₁, h₁⟩ := GlobalTheory.T.pointwise_cocycle_on_cover_extends_up_to_coboundary R _ K (parCov W x) (iSup_parCov hW x) _
      (GlobalTheory.PtExt.parCoc_isCoc R A B K W J a _ n ha (fun i ↦ hfv _) hn D x)
    obtain ⟨m, d, c, k₂, h₂⟩ := GlobalTheory.T.cocycle_spec_prod_abelian_cohomologous_sum_mul H R B g hB hg D u hu
    refine ⟨m, d, c, fun E _ _ z ↦ k₁ E z + k₂ E z, ?_⟩
    intro E _ _ E' _ _ ψ z hz
    have e₁ := h₁ E E' ψ z hz
    have e₂ := h₂ E E' ψ z (sm_whole z)
    simp only [Fn1.add, Fn1.neg] at e₁ e₂ ⊢
    rw [map_add (f := _)]
    linear_combination e₁ + e₂
  choose m d c k hk using key
  refine ⟨fun D _ _ x ↦ ∑ j, d D x j * algebraMap R D (y ⟨_, hP (c D x j)⟩), ?_⟩
  intro D _ _ D' _ _ φ x _
  have hcob : IsCob (parCov W (spOver φ ≫ x))
      (sumMul (Sum.elim (d D' (spOver φ ≫ x)) (Sum.elim (fun i ↦ -φ (d D x i)) (fun i ↦ -a i D D' φ x)))
        (fun i ↦ fv (Sum.elim (c D' (spOver φ ≫ x)) (Sum.elim (c D x) β) i)))
      (fun E _ _ z ↦ k D x E (z ≫ spOver φ ▷ B) - k D' (spOver φ ≫ x) E z) := by
    intro E _ _ E' _ _ ψ z hz
    have e₁ := hk D' (spOver φ ≫ x) E E' ψ z hz
    have e₂ := hk D x E E' ψ (z ≫ spOver φ ▷ B) (sm_parCov φ x z hz)
    have e₃ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      (GlobalTheory.PtExt.parCoc_spOver R A B J a (fun i ↦ fv (β i)) n ha D D' φ x)
    have e₄ := congrArg (fun u : Fn1 (SpAlg R D' ⊗ B) ↦ u E E' ψ z)
      ((GlobalTheory.PtExt.SumMulFacts.main R D B _ (d D x) (fun i ↦ fv (c D x i))).2 D' φ)
    rw [sumMul_elim]
    simp only [Fn1.add, Fn1.neg, Fn1.pull] at e₁ e₂ e₃ e₄
    beta_reduce
    rw [map_sub, Category.assoc]
    linear_combination e₂ - e₁ + e₃ + e₄
  have h0 := GlobalTheory.T.sum_mul_hodgeFil_eq_zero_of_deRham_coboundary H R B g hB hg y hy D' _ _ _ (fun i ↦ hP _)
    (GlobalTheory.PtExt.isCob_whole_of_isCob_cover R _ K _ (iSup_parCov hW (spOver φ ≫ x)) _
      ((GlobalTheory.PtExt.SumMulFacts.main R D' B _ _ _).1 fun i ↦ hfv _) _ hcob)
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, neg_mul, Finset.sum_neg_distrib] at h0

  simp only [map_sum, map_mul, AlgHom.commutes]
  linear_combination -h0

end GlobalTheory.PtExt.OrthPt
end
end
end
