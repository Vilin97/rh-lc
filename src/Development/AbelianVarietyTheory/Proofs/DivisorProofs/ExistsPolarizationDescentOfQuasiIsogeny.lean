module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirigidifiedPullbackMulPairIsoTensorPowSqStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundle
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
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearChangeEulerProduct
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelObjectLoweredLevel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidified
import Mathlib.RingTheory.WittVector.IsPoly
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedKthRootPullbackBundleStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle : ∀ (Y : Scheme.{0}) (A D : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj D] (Q : LB (A ⊗ D).left) (h : A ⟶ D) (k : ℕ) (X : Scheme.{0}) (M : LB X) (c : (A ⊗ A).left ⟶ X), IsAbelianScheme A → IsAbelianScheme D → GlobalTheory.AbDual.IsDual A D Q → GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) → IsMonHom h → 0 < k → IsUnit (k : Γ(Y, ⊤)) → M.IsLB → LBIso (M.pull c) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) → ∀ (U : Scheme.{0}) (t : U ⟶ Y) (AU : Over U) [GrpObj AU] [IsCommMonObj AU] (φ : AU.left ⟶ A.left) (φ₂ : (G2 AU).left ⟶ (G2 A).left), IsGrpPullback AU A t φ → IsSquare φ φ₂ → (∀ (T : Over Y) (s : T.left ⟶ U), s ≫ t = T.hom → ∀ a : T ⟶ A, a ^ k = 1 → a ≫ h = 1) → ∃ P : LB (G2 AU).left, P.IsLB ∧ (∃ t : (P.pull (lift (1 : AU ⟶ AU) (𝟙 AU)).left).Gen, t.IsGen) ∧ (∃ t : (P.pull (lift (𝟙 AU) (1 : AU ⟶ AU)).left).Gen, t.IsGen) ∧ LBIso (M.pull (φ₂ ≫ c)) (lbPow P k) := by
  first | (exact @GlobalTheory.KthRoot.exists_birigid_kth_root) | (exact GlobalTheory.KthRoot.exists_birigid_kth_root) | (intros; apply GlobalTheory.KthRoot.exists_birigid_kth_root <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualAbelianScheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj


theorem _root_.GlobalTheory.T.exists_dual_abelian_scheme : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  first | (exact @GlobalTheory.DualHomPull.exists_dual_hom) | (exact GlobalTheory.DualHomPull.exists_dual_hom) | (intros; apply GlobalTheory.DualHomPull.exists_dual_hom  <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleProdIsoOfPowIsoBirigidifiedStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor


theorem _root_.GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ) (P₁ P₂ : LB (G2 A).left), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → P₁.IsLB → (∃ t : (P₁.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₁.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → P₂.IsLB → (∃ t : (P₂.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P₂.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso (lbPow P₁ k) (lbPow P₂ k) → LBIso P₁ P₂ := by
  first | (exact @GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (exact GlobalTheory.BirigidRoot.iso_of_lbPow_iso) | (intros; apply GlobalTheory.BirigidRoot.iso_of_lbPow_iso  <;> assumption)
end
end

-- Source module: Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPolarizationDescentOfQuasiIsogeny

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hce hB hq hker
  obtain ⟨e, rfl⟩ := hce
  obtain ⟨hψ, hψ', h1, h2⟩ := hq
  haveI := hψ
  haveI := hψ'
  have hc0 : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hP := o.isLB
  have hlb : ∀ m, (Hecke.lbPow o.P m).IsLB := fun m => by
    unfold Hecke.lbPow
    exact LB.isLB_linComb hP _ _
  obtain ⟨Dd, _, Q, h, hD, hdual, hadd, hh, hiso⟩ :=
    GlobalTheory.T.exists_dual_abelian_scheme Y B o.A ψ' o.P hB o.ab hψ' hP o.rig₁ o.rig₂
  have hQ := hdual.isLB
  have etens : (ψ' ⊗ₘ ψ') = lift (fst B B ≫ ψ') (snd B B ≫ ψ') := by
    ext <;> simp
  have esq : Hecke.sq2 ψ' = Over.Hom.left (ψ' ⊗ₘ ψ') := by
    rw [etens]
    rfl
  have kiso := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hQ _)).2 hiso
  rw [GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.cls_pull hQ] at kiso
  have hkerh : ∀ (T : Over Y) (σ : T.left ⟶ Y), σ ≫ 𝟙 Y = T.hom →
      ∀ a : T ⟶ B, a ^ (p ^ e) = 1 → a ≫ h = 1 := by
    intro T σ hσ a ha
    have ha3 : a ^ (p ^ e) ^ 3 = 1 := by
      rw [show (p ^ e) ^ 3 = p ^ e * (p ^ e) ^ 2 by ring, pow_mul, ha, one_pow]
    have htriv := (hker T σ hσ a ha3).2 ha
    apply hdual.eq_one
    have e1 : lift (fst B T) (snd B T ≫ a ≫ h) =
        lift (fst B T) (snd B T ≫ a) ≫ lift (fst B B) (snd B B ≫ h) := by
      ext <;> simp
    have e2 : lift (fst B T ≫ ψ') (snd B T ≫ a ≫ ψ') =
        lift (fst B T) (snd B T ≫ a) ≫ (ψ' ⊗ₘ ψ') := by
      rw [etens]
      ext <;> simp
    have k2 := (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP _)).2 htriv
    rw [GlobalTheory.CechPic.cls_pull hP, e2, Over.comp_left, GlobalTheory.CechPic.pull_comp, kiso,
      ← GlobalTheory.CechPic.pull_comp, ← Over.comp_left, ← e1, ← GlobalTheory.CechPic.cls_pull hQ _ (pull_isLB hQ _)] at k2
    exact (GlobalTheory.CechPic.cls_eq_zero_iff _).1 k2
  have hunit : IsUnit (((p ^ e : ℕ) : Γ(Y, ⊤))) := by
    have h0 : IsUnit ((p : ℕ) : Γ(Sp R, ⊤)) := by
      have := hp.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this
    have h3 := h0.map s.appTop.hom
    rw [map_natCast] at h3
    simpa using h3.pow e
  obtain ⟨P', hP'lb, hr1, hr2, hP'iso⟩ :=
    GlobalTheory.T.exists_birigidified_kth_root_pullback_bundle Y B Dd Q h (p ^ e) _ o.P (Over.Hom.left (ψ' ⊗ₘ ψ')) hB hD hdual hadd hh hc0 hunit hP
      hiso Y (𝟙 Y) B (𝟙 _) (𝟙 _) (GlobalTheory.SiegLower.isGrpPullback_id B) ⟨by simp, by simp⟩ hkerh
  have kP' := (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (GlobalTheory.isLB_lbPow hP'lb _)).2 hP'iso
  rw [Category.id_comp, GlobalTheory.CechPic.cls_lbPow hP'lb, GlobalTheory.CechPic.cls_pull hP, ← esq] at kP'
  have hP2 : (P'.pull (Hecke.sq2 ψ)).IsLB := pull_isLB hP'lb _
  have sqc : Hecke.sq2 (ψ ≫ ψ') = Hecke.sq2 ψ ≫ Hecke.sq2 ψ' := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have eL1 : Over.Hom.left (lift (1 : o.A ⟶ o.A) (𝟙 o.A)) ≫ Hecke.sq2 ψ =
      Over.Hom.left ψ ≫ Over.Hom.left (lift (1 : B ⟶ B) (𝟙 B)) := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  have eL2 : Over.Hom.left (lift (𝟙 o.A) (1 : o.A ⟶ o.A)) ≫ Hecke.sq2 ψ =
      Over.Hom.left ψ ≫ Over.Hom.left (lift (𝟙 B) (1 : B ⟶ B)) := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    ext <;> simp
  refine ⟨P', ⟨hP'lb, hr1, hr2⟩, ?_, ?_⟩
  · rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP _) (by unfold Hecke.lbPow; exact LB.isLB_linComb hP'lb _ _),
      GlobalTheory.BirigidPow.cls_lbPow hP'lb, GlobalTheory.CechPic.cls_pull hP, kP']
  · refine GlobalTheory.T.lineBundle_prod_iso_of_pow_iso_birigidified Y o.A (p ^ e) _ _ o.ab hc0 hunit (hlb _) ?_ ?_ hP2 ?_ ?_ ?_
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (hlb _) _), GlobalTheory.CechPic.cls_pull (hlb _),
        GlobalTheory.BirigidPow.cls_lbPow hP, map_nsmul, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o.rig₁, nsmul_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB (hlb _) _), GlobalTheory.CechPic.cls_pull (hlb _),
        GlobalTheory.BirigidPow.cls_lbPow hP, map_nsmul, ← GlobalTheory.CechPic.cls_pull hP _ (pull_isLB hP _),
        (GlobalTheory.CechPic.cls_eq_zero_iff _).2 o.rig₂, nsmul_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _), GlobalTheory.CechPic.cls_pull hP2,
        GlobalTheory.CechPic.cls_pull hP'lb, ← GlobalTheory.CechPic.pull_comp, eL1, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ (pull_isLB hP'lb _), (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hr1, map_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _), GlobalTheory.CechPic.cls_pull hP2,
        GlobalTheory.CechPic.cls_pull hP'lb, ← GlobalTheory.CechPic.pull_comp, eL2, GlobalTheory.CechPic.pull_comp,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ (pull_isLB hP'lb _), (GlobalTheory.CechPic.cls_eq_zero_iff _).2 hr2, map_zero]
    · rw [← GlobalTheory.CechPic.cls_eq_iff (GlobalTheory.isLB_lbPow (hlb _) _) (GlobalTheory.isLB_lbPow hP2 _),
        GlobalTheory.CechPic.cls_lbPow (hlb _), GlobalTheory.CechPic.cls_lbPow hP2, GlobalTheory.BirigidPow.cls_lbPow hP, smul_smul,
        ← pow_two, ← GlobalTheory.BirigidPow.cls_lbPow hP _ (hlb _),
        (GlobalTheory.CechPic.cls_eq_iff (hlb _) (pull_isLB hP _)).2
          (GlobalTheory.T.lbIso_lbPow_sq_pull_sq2_of_isGen_of_relAmple Y o.A o.ab o.P hP o.rig₁ o.rig₂ o.ample (p ^ e)),
        ← h1, sqc, GlobalTheory.CechPic.cls_pull hP, GlobalTheory.CechPic.pull_comp, kP', map_nsmul,
        ← GlobalTheory.CechPic.cls_pull hP'lb _ hP2]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationDescentOfQuasiIsogeny

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  first | exact @UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny | exact UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny
end
end
