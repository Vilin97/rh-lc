module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MapsAtIdIsoPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPowDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.PsiInOfIsPullDeg
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SymBox
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBimultPow
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValPsiZero

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInProdOfIsPowDeg

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace PsiInProd

theorem map_ideal_prod {A B K : Type} [CommRing A] [CommRing B] [Fintype K] (f : A →+* B) (J : K → Ideal A) :
    (∏ i, J i).map f = ∏ i, (J i).map f :=
  map_prod (Ideal.mapHom f) J Finset.univ

end PsiInProd


open PsiInPull PsiInPow PsiInProd in
theorem psiIn_prod_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j) (x : D'.X) (J : Fin j → Ideal R),
    (∀ i, D.PsiIn (pD.xe x i) (J i)) → D'.PsiIn x (∏ i, J i) := by
  intro R _ _ j D D' pD χ J H
  classical
  refine psiIn_of_gs D' χ _ fun q V' hV' hle' z hz => exists_of_locally _ z _ V' hV' hz fun v hv => ?_
  have : IsDominant (jK R) := isDominant_jK
  choose pick hpk using fun p : Spec (CommRingCat.of R) ⟶ D.P.A.left => exists_chart D.P.isLB (p v)
  have hcp : ∀ i, (D'.c χ).left ≫ (pD.pw.pr i).left = (D.c (pD.xe χ i)).left := fun i =>
    congrArg (fun m => m.left) (pD.c_pr χ i)
  have hxp : ∀ i, D'.xK χ ≫ (pD.pw.pr i).left = D.xK (pD.xe χ i) := fun i =>
    (Category.assoc (jK R) _ _).trans (congrArg (jK R ≫ ·) (hcp i))
  let p : Fin j → D.P.L.ι := fun i => pick (D.c (pD.xe χ i)).left
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, hVp⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
    (show v ∈ (V' ⊓ LB.wchart D.P.L (fun i => (D.c (pD.xe χ i)).left) p : (Spec (CommRingCat.of R)).Opens) from
      ⟨hv, Set.mem_iInter.2 fun i => hpk _⟩)
    (V' ⊓ LB.wchart D.P.L (fun i => (D.c (pD.xe χ i)).left) p : (Spec (CommRingCat.of R)).Opens).isOpen
  have hVV : V ≤ V' := fun y hy => (hVp hy).1
  have hVi : ∀ i, V ≤ (D.c (pD.xe χ i)).left ⁻¹ᵁ D.P.L.U (p i) := fun i y hy => Set.mem_iInter.1 (hVp hy).2 i
  have hzV : jK R z ∈ V := jK_mem z _ (fun h0 => (h0.le hvV : v ∈ (⊥ : (Spec (CommRingCat.of R)).Opens)))
  choose r hr er using fun i => gs_of_psiIn D _ _ (H i) (p i) V hV (hVi i) z hzV
  obtain ⟨I, hI, eI⟩ := exists_good D.P.L D.P.isLB (Z := (TK R).left) z (fun i => D.xK (pD.xe χ i)) p
    (fun a b h => congrArg pick (ext_of_isDominant_of_isSeparated (X := Spec (CommRingCat.of R)) D.P.A.hom
      ((Over.w (D.c (pD.xe χ a))).trans (Over.w (D.c (pD.xe χ b))).symm) (jK R) h))
    (fun i => hVi i hzV)
  obtain ⟨I', hI', eI'⟩ := exists_good D'.P.L D'.P.isLB (Z := (TK R).left) z (K := PUnit) (fun _ => D'.xK χ)
    (fun _ => q) (fun _ _ _ => rfl) (fun _ => hle' hz)
  have e0 : I' (D'.xK χ) = q := eI' PUnit.unit
  obtain ⟨b, hb, hcorr⟩ := pD.w_psi χ
  have e1 := QBox.mapsAt_val pD.w _ _ _ b hb z hI hI'
  have e2 := (val_corr hI hcorr (𝟙 _)).trans (QBox.val_finProdGen _ _ _ _ _ hI)
  have ep : (fun i => I (D'.xK χ ≫ (pD.pw.pr i).left)) = p := funext fun i => (congrArg I (hxp i)).trans (eI i)
  rw [ep, e0, zpow_neg_one, eq_inv_mul_iff_mul_eq, e2,
    val_of (D'.psi χ) _ z I' (fun _ => q) (fun _ => (congrArg I' (Category.id_comp _)).trans e0)] at e1
  have hU : V ≤ (D'.c χ).left ⁻¹ᵁ (LB.wchart D.P.L (fun i => (pD.pw.pr i).left) p ⊓ D'.P.L.U q) := fun y hy =>
    ⟨Set.mem_iInter.2 fun i => (congrArg (fun m => m y ∈ D.P.L.U (p i)) (hcp i)).mpr (hVi i hy), hle' (hVV hy)⟩
  refine ⟨V, hVV, hvV, (res hU (pullU (D'.c χ).left _ (pD.w.s (p, q)))).val * ∏ i, r i,
    Ideal.mul_mem_left _ _ ?_, ?_⟩
  · rw [map_ideal_prod]
    exact Ideal.prod_mem_prod fun i _ => hr i
  · refine Eq.trans ?_ (congrArg Units.val e1)
    refine (gs_mul _ _ _ hzV _ _).trans (congrArg₂ (· * ·) ?_ ?_)
    · exact (gs_unit _ _ _ hzV _).trans (congrArg Units.val ((gm_res _ _ hU hzV _).trans
        (gm_pull (jK R) (D'.c χ).left z _ (hU hzV) _)))
    · rw [gs_prod _ _ _ hzV, Units.coe_prod]
      refine Finset.prod_congr rfl fun i _ => (er i).trans (congrArg Units.val ?_)
      exact (val_of (D.psi (pD.xe χ i)) _ z I (fun _ => p i) (fun _ => (congrArg I (Category.id_comp _)).trans (eI i))).symm

end GlobalTheory
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PowDegData

theorem psiIn_top {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) (χ : D.toPre.X) :
    D.toPre.PsiIn χ ⊤ := by
  by_cases h : χ = 0
  · subst h
    exact (GlobalTheory.PsiZero.main R D.toPre).1 D.tau_bimult
  · exact (GlobalTheory.PsiZero.main R D.toPre).2 χ I ⊤ le_top (D.psi_pos χ h)

theorem psiIn_of_component {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (D : DegData R I) {j : ℕ}
    {D' : DegPre R} (pD : IsPowDeg D' D.toPre j) (x : D'.X) (J : Ideal R) (i : Fin j)
    (h : D.toPre.PsiIn (pD.xe x i) J) : D'.PsiIn x J := by
  classical
  have H := GlobalTheory.psiIn_prod_of_isPowDeg R j D.toPre D' pD x (fun k => if k = i then J else ⊤) (fun k => by
    by_cases hk : k = i
    · subst hk
      simpa using h
    · simpa [hk] using psiIn_top D (pD.xe x k))
  refine (GlobalTheory.PsiZero.main R D').2 x _ J ?_ H
  refine (Ideal.prod_le_inf).trans ((Finset.inf_le (Finset.mem_univ i)).trans ?_)
  simp

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (j : ℕ), ∃ D' : DegData R I, Nonempty (IsPowDeg D'.toPre D.toPre j) := by
  intro hG R _ _ I D j
  obtain ⟨D', ⟨pD⟩⟩ := GlobalTheory.PowDegPre.exists_pow R D.toPre j
  refine ⟨⟨D', GlobalTheory.PsiEvenBox.main hG R j D.toPre D' pD D.psi_even,
    GlobalTheory.TauBimultBox.tauBimult_pow hG R j D.toPre D' pD D.tau_bimult, fun x hx => ?_, fun n => ?_⟩, ⟨pD⟩⟩
  · have : pD.xe x ≠ 0 := fun h => hx (pD.xe.map_eq_zero_iff.1 h)
    obtain ⟨i, hi⟩ := Function.ne_iff.1 this
    exact psiIn_of_component D pD x I i (D.psi_pos _ hi)
  · have hf : (Set.pi Set.univ fun _ : Fin j => {χ : D.toPre.X | ¬ D.toPre.PsiIn χ (I ^ n)}).Finite :=
      Set.Finite.pi fun _ => D.psi_tendsto n
    refine (hf.preimage pD.xe.injective.injOn).subset fun x hx i _ hi => ?_
    exact hx (psiIn_of_component D pD x _ i hi)

end GlobalTheory.PowDegData
end
end
