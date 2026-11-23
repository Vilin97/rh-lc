module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueCombOfIndependentSpecialFibre
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Modules.Sheaf
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Tactic.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOfValFGeneric
import Mathlib.Tactic.Basify

-- Source module: Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisAlongOfIndependentFibres

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.GenericSectionBasis

namespace GlobalTheory.TraitBasis

theorem toStk_valF_eq_gs {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) : toStk z (valF x U a) = gs x z U a := by
  rw [valF, dite_eq_left ((top_le_iff_mem x U z).2 h), gs_eq x z U h]
  show ((Sp F).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp F).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem toStk_eq_cst {F : Type} [Field F] (z : Sp F) (a : F) : toStk z a = cst (𝟙 (Sp F)) z a := by
  rw [cst, gs_eq _ z ⊤ trivial]; rfl

theorem gs_eq_zero_of_notMem {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F)
    (h : x z ∈ U) (a : Γ(X, U)) (ha : x z ∉ X.basicOpen a) : gs x z U a = 0 := by
  by_cases h0 : valF x U a = 0
  · rw [← toStk_valF_eq_gs x U z h, h0, map_zero]
  · refine (ha ?_).elim
    have u : IsUnit (gs x z U a) := by
      rw [← toStk_valF_eq_gs x U z h]; exact (IsUnit.mk0 _ h0).map _
    rw [gs_stalkMap x z U h, isUnit_map_iff, gs_eq (𝟙 X) (x z) U h] at u
    exact (X.mem_basicOpen a (x z) h).2 u

theorem map_eq_zero_of_points {X B Y : Scheme.{0}} {M : LB X} (π : X ⟶ B) {n : ℕ} (b : Fin n → LB.Sec M)
    {K : Type} [Field K]
    (H : ∀ (x : Sp K ⟶ B) (c : Fin n → K),
      (∀ (g : Sp K ⟶ X) j, g ≫ π = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0)
    {R : Type} [CommRing R] {χ : Sp R ⟶ B} {p : Y ⟶ Sp R} {r : Y ⟶ X} (hp : IsPullback r p π χ)
    (κ : R →+* K) (c : Fin n → R)
    (h0 : ∀ (g : Sp K ⟶ Y) (z : Sp K) j, g ≫ p = spMap κ → (g ≫ r) z ∈ M.U j →
      ∑ i, cst (g ≫ p) z (c i) * gs (g ≫ r) z (M.U j) ((b i).f j) = 0) (i : Fin n) : κ (c i) = 0 := by
  refine congrFun (H (spMap κ ≫ χ) (fun i => κ (c i)) fun g j hg => ?_) i
  obtain ⟨g', rfl, h₂⟩ : ∃ g' : Sp K ⟶ Y, g' ≫ r = g ∧ g' ≫ p = spMap κ :=
    ⟨hp.lift g (spMap κ) hg, hp.lift_fst _ _ _, hp.lift_snd _ _ _⟩
  let z : Sp K := (default : PrimeSpectrum K)
  by_cases hz : (g' ≫ r) z ∈ M.U j
  · apply (toStk z).injective

    rw [map_zero, ← h0 g' z j h₂ hz, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, toStk_valF_eq_gs _ _ z hz, toStk_eq_cst, h₂, H1.gs_spec]
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [valF, dite_eq_right (fun h => hz ((top_le_iff_mem _ _ z).1 h)), mul_zero]

theorem exists_comb_of_independent {F : Type} [Field F] {Y : Scheme.{0}} {M : LB Y} {p : Y ⟶ Sp F} {n : ℕ}
    (H : HasBasis M p n) (β : Fin n → LB.Sec M)
    (ind : ∀ c : Fin n → F, (∀ j, ∑ i, Out.resTop _ (Out.scal p (c i)) * (β i).f j = 0) → c = 0)
    (s : LB.Sec M) : ∃ c, IsComb p β c s := by
  obtain ⟨e, he⟩ := H
  choose m hm using fun i => (he (β i)).exists
  have key : ∀ (c : Fin n → F) j, ∑ i, Out.resTop _ (Out.scal p (c i)) * (β i).f j =
      ∑ k, Out.resTop _ (Out.scal p (Matrix.vecMul c (Matrix.of m) k)) * (e k).f j := fun c j => by

    simp only [fun i => hm i j, SaturatedSections.cst_eq, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul, Matrix.of_apply, _root_.mul_assoc]
    exact Finset.sum_comm
  have inj : Function.Injective (Matrix.vecMulLinear (Matrix.of m)) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro c hc
    refine ind c fun j => ?_
    have hc' : Matrix.vecMul c (Matrix.of m) = 0 := hc
    rw [key, hc']
    simp only [SaturatedSections.cst_eq, Pi.zero_apply, map_zero, zero_mul, Finset.sum_const_zero]
  obtain ⟨d, hd, -⟩ := he s
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.1 inj d
  refine ⟨c, fun j => ?_⟩
  have hc' : Matrix.vecMul c (Matrix.of m) = d := hc
  rw [key, hc']
  exact hd j

theorem existsUnique_comb {X B Y A G : Scheme.{0}} {L : LB G} (hL : L.IsLB) (q : X ⟶ G) (π : X ⟶ B) (N : ℤ)
    {n : ℕ} (b : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => q) (fun _ => N)))
    (H : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ B) (c : Fin n → K),
      (∀ (g : Sp K ⟶ X) j, g ≫ π = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0)
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {χ : Sp W ⟶ B} {p : Y ⟶ Sp W} [Flat p]
    {r : Y ⟶ X} (hp : IsPullback r p π χ) {a : A ⟶ Sp (FractionRing W)} {ρ : A ⟶ Y}
    (hρ : IsPullback ρ a p (Out.jK W)) {q' : Y ⟶ G} (hq : r ≫ q = q') {φ : A ⟶ G} (hφ : ρ ≫ q' = φ)
    (hb : HasBasis (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => N)) a n)
    (s : Fin n → LB.Sec (LB.LinComb L (fun _ : Fin 1 => q') (fun _ => N)))
    (hs : ∀ i (Z : Scheme.{0}) (u : Z ⟶ Y) (z : Z) j, u z ∈ LB.wchart L (fun _ : Fin 1 => q') j →
      gs u z (LB.wchart L (fun _ : Fin 1 => q') j) ((s i).f j) =
        gs (u ≫ r) z (LB.wchart L (fun _ : Fin 1 => q) j) ((b i).f j))
    (t : LB.Sec (LB.LinComb L (fun _ : Fin 1 => q') (fun _ => N))) : ∃! c : Fin n → W, IsComb p s c t := by
  subst hq hφ
  refine existsUnique_comb_of_independent_special_fibre W Y p _ (DVR.linComb_isLB L hL _ _) n s
    (fun c hc i => ?_) t ?_
  · let k := IsLocalRing.ResidueField W
    let κ : W →+* AlgebraicClosure k := (algebraMap k (AlgebraicClosure k)).comp (IsLocalRing.residue W)
    have hκ : ∀ w, κ w = 0 ↔ w ∈ IsLocalRing.maximalIdeal W := fun w =>
      (map_eq_zero_iff _ (algebraMap k (AlgebraicClosure k)).injective).trans (IsLocalRing.residue_eq_zero_iff w)
    refine (hκ _).1 (map_eq_zero_of_points π b (H _) hp κ c (fun g z j hg hz => ?_) i)
    have hz' : g z ∈ LB.wchart L (fun _ : Fin 1 => r ≫ q) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
    have hcl : p (g z) = IsLocalRing.closedPoint W := by
      have e : p (g z) = spMap κ z := congrArg (fun u : Sp (AlgebraicClosure k) ⟶ Sp W => u z) hg
      rw [e]
      refine PrimeSpectrum.ext (Ideal.ext fun w => ?_)
      have e₂ : z = (⊥ : PrimeSpectrum (AlgebraicClosure k)) :=
        Subsingleton.elim (α := PrimeSpectrum (AlgebraicClosure k)) _ _
      subst e₂
      exact hκ w
    have e := gs_eq_zero_of_notMem g _ z hz' _ (hc j (g z) hz' hcl)
    refine Eq.trans ?_ ((gs_comb p s c g z j hz').symm.trans e)
    exact Finset.sum_congr rfl fun i _ => congrArg _ (hs i _ g z j hz').symm
  · choose s' hs' using fun i => exists_pull_gs (s i) ρ (fun _ : Fin 1 => ρ ≫ r ≫ q) (fun _ => rfl)
    obtain ⟨t', ht'⟩ := exists_pull_gs t ρ (fun _ : Fin 1 => ρ ≫ r ≫ q) (fun _ => rfl)
    obtain ⟨c, hc⟩ := exists_comb_of_independent hb s' (fun c hc => funext fun i => by
      let κ := algebraMap (FractionRing W) (AlgebraicClosure (FractionRing W))
      refine κ.injective ((map_eq_zero_of_points π b (H _) (hρ.paste_horiz hp) κ c
        (fun g z j hg hz => ?_) i).trans (map_zero κ).symm)
      have hz' : g z ∈ LB.wchart L (fun _ : Fin 1 => ρ ≫ r ≫ q) j :=
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
      have hz₂ : (g ≫ ρ) z ∈ LB.wchart L (fun _ : Fin 1 => r ≫ q) j :=
        Set.mem_iInter.2 fun k => Set.mem_iInter.1 hz k
      have e := gs_comb a s' c g z j hz'
      rw [hc j] at e
      refine Eq.trans ?_ (e.symm.trans ((gs_eq g z _ hz' _).trans ((congrArg _ (map_zero _)).trans (map_zero _))))
      refine Finset.sum_congr rfl fun i _ => congrArg _ (Eq.symm ?_)
      exact (hs' i _ g z j hz').trans ((hs i _ (g ≫ ρ) z j hz₂).trans (by rw [Category.assoc]; rfl))) t'
    obtain ⟨⟨w, hw⟩, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors W) c
    choose d hd using hd
    refine ⟨w, d, nonZeroDivisors.ne_zero hw, fun j => ?_⟩
    have : IsDominant (Out.jK W) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
      (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective W (FractionRing W))).le.trans bot_le)⟩
    have := IsSchemeTheoreticallyDominant.of_isDominant (Out.jK W)
    have : IsSchemeTheoreticallyDominant ρ := IsSchemeTheoreticallyDominant.of_isPullback hρ.flip
    have : QuasiCompact ρ := MorphismProperty.of_isPullback (P := @QuasiCompact) hρ.flip inferInstance
    refine ρ.app_injective _ (fn_ext fun y hy => ?_)
    refine (gs_pull (𝟙 _) ρ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) ρ y _ hy _).symm)
    have hy' : (𝟙 A : A ⟶ A) y ∈ LB.wchart L (fun _ : Fin 1 => ρ ≫ r ≫ q) j :=
      Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
    have cc : ∀ v : W, cst ((𝟙 A ≫ ρ) ≫ p) y v = cst (𝟙 A ≫ a) y (algebraMap W (FractionRing W) v) := fun v => by
      rw [Category.assoc, hρ.w, ← Category.assoc]
      exact cst_comp _ _ y v
    refine Eq.trans ?_ (gs_comb p s d (𝟙 A ≫ ρ) y j hy).symm
    refine (gs_mul (𝟙 A ≫ ρ) y _ hy _ _).trans ?_
    refine (congrArg₂ (· * ·) (GlobalTheory.IndivisibleSection.gs_scal p (𝟙 A ≫ ρ) y _ hy w)
      ((ht' _ (𝟙 A) y j hy').symm.trans ((congrArg (gs (𝟙 A) y _) (hc j)).trans
        (gs_comb a s' c (𝟙 A) y j hy')))).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [cc, cc, hd i, Algebra.smul_def, H1.cst_mul, _root_.mul_assoc]
    exact congrArg (fun v => _ * (_ * v)) (hs' i _ (𝟙 A) y j hy')

end GlobalTheory.TraitBasis


open GlobalTheory.TraitBasis in
theorem GlobalTheory.basisAlong_of_independent_fibres : Out.Laws → ∀ (Z : Scheme.{0}) (G : Over Z) [GrpObj G] (L : LB G.left) (N n : ℕ) (T : Over Z) (b : Fin n → LB.Sec (Out.LPow G L (N : ℤ) T)), L.IsLB → IsSemiAbelian G → 1 ≤ N → (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ T.left) (c : Fin n → K), (∀ (g : Sp K ⟶ (T ⊗ G).left) j, g ≫ (fst T G).left = x → ∑ i, c i * valF g _ ((b i).f j) = 0) → c = 0) → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (χ : Sp W ⟶ T.left) (A : Out.PolAV (Sp (FractionRing W))) (φ : A.A.left ⟶ G.left), IsGrpPullback A.A G (Out.jK W ≫ χ ≫ T.hom) φ → LBIso A.L (L.pull φ) → n = N ^ A.g → GlobalTheory.LN.BasisAlong G L N (Over.homMk χ rfl : Over.mk (χ ≫ T.hom) ⟶ T) b := by
  intro laws Z G _ L N n T b hL hG hN H W _ _ _ hW χ A φ hφ hiso hn t
  have := hW.1
  have := hG.smooth
  let T' : Over Z := Over.mk (χ ≫ T.hom)
  let h : T' ⟶ T := Over.homMk χ rfl
  have P₀ : IsPullback (snd T G).left (fst T G).left G.hom T.hom := (IsPullback.of_hasPullback T.hom G.hom).flip
  have P₁ : IsPullback (snd T' G).left (fst T' G).left G.hom (χ ≫ T.hom) :=
    (IsPullback.of_hasPullback T'.hom G.hom).flip
  have e₁ : (h ▷ G).left ≫ (snd T G).left = (snd T' G).left := congrArg CommaMorphism.left (whiskerRight_snd h G)
  have e₂ : (h ▷ G).left ≫ (fst T G).left = (fst T' G).left ≫ χ :=
    congrArg CommaMorphism.left (whiskerRight_fst h G)
  have hp : IsPullback (h ▷ G).left (fst T' G).left (fst T G).left χ :=
    IsPullback.of_right (by rw [e₁]; exact P₁) e₂ P₀
  let ρ : A.A.left ⟶ (T' ⊗ G).left := P₁.lift φ (A.A.hom ≫ Out.jK W) (hφ.1.w.trans (Category.assoc _ _ _).symm)
  have r₁ : ρ ≫ (snd T' G).left = φ := P₁.lift_fst _ _ _
  have hρ : IsPullback ρ A.A.hom (fst T' G).left (Out.jK W) :=
    IsPullback.of_right (by rw [r₁]; exact hφ.1) (P₁.lift_snd _ _ _) P₁
  have : Flat (X := (T' ⊗ G).left) (Y := Sp W) (fst T' G).left :=
    MorphismProperty.of_isPullback (P := @Flat) P₁ inferInstance
  have hb : HasBasis (LB.LinComb L (fun _ : Fin 1 => φ) (fun _ => (N : ℤ))) A.A.hom n := by
    obtain ⟨w, hw⟩ := hiso
    have i := iso_linComb ((isGen_iff w).1 hw) (fun _ : Fin 1 => 𝟙 A.A.left) (fun _ => (N : ℤ))
    simp only [Category.id_comp] at i
    rw [hn]
    exact (hasBasis_field A N laws.secBaseChange hN).of_iso (DVR.linComb_isLB L hL _ _)
      (DVR.linComb_isLB _ A.isLB _ _) i.symm
  choose s hs using fun i => exists_pull_gs (b i) (h ▷ G).left (fun _ : Fin 1 => (snd T' G).left) (fun _ => e₁)
  have main := TraitBasis.existsUnique_comb hL (snd T G).left (fst T G).left (N : ℤ) b H hp hρ e₁ r₁ hb s hs t
  let ε : W ≃+* Γ(Sp W, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of W)).symm.commRingCatIsoToRingEquiv
  have key : ∀ c : Fin n → W, IsComb (fst T' G).left s c t ↔ GlobalTheory.LN.Lin G L N h b (fun i => ε (c i)) t := fun c => by
    obtain ⟨u, hu⟩ := GenericSectionBasis.exists_comb (F := W) (fst T' G).left s c
    have ev : ∀ (z : (T' ⊗ G).left) J, Good L z J →
        sval (L := L) (φ := fun _ : Fin 1 => (snd T' G).left) (ε := fun _ => (N : ℤ)) u (𝟙 _) z J =
        ∑ i, gs (fst T' G).left z ⊤ (ε (c i)) *
          sval (L := L) (φ := fun _ : Fin 1 => (snd T G).left) (ε := fun _ => (N : ℤ)) (b i) (h ▷ G).left z J := by
      intro z J hJ
      have hm := hJ.mem (fun _ : Fin 1 => (snd T' G).left) (𝟙 _)
      refine (congrArg (gs (𝟙 _) z _) (hu _)).trans ((gs_comb (F := W) (fst T' G).left s c (𝟙 _) z _ hm).trans ?_)
      refine Finset.sum_congr rfl fun i _ => congrArg₂ (· * ·) ?_ ?_
      · rw [Category.id_comp]; rfl
      · refine (hs i _ (𝟙 _) z _ hm).trans ?_
        rw [sval_of (b i) (h ▷ G).left z J (fun _ => J (𝟙 _ ≫ (snd T' G).left))
          (fun _ => by rw [e₁, Category.id_comp]), Category.id_comp (h ▷ G).left]
    constructor
    · intro hc z J hJ
      refine Eq.trans ?_ (ev z J hJ)
      exact congrArg (gs (𝟙 _) z _) ((hc _).trans (hu _).symm)
    · intro hc j
      exact (sec_ext_val hL (fun y J hJ => (hc y J hJ).trans (ev y J hJ).symm) j).trans (hu j)
  obtain ⟨c, hc, hu⟩ := main
  refine ⟨fun i => ε (c i), (key c).1 hc, fun c' hc' => ?_⟩
  obtain ⟨d, rfl⟩ : ∃ d : Fin n → W, c' = fun i => ε (d i) :=
    ⟨fun i => ε.symm (c' i), funext fun i => (ε.apply_symm_apply _).symm⟩
  rw [hu d ((key d).2 hc')]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.FoundationProofs.LinearIndependentOfDetMemNonZeroDivisors

section

@[expose] public section

open Module Submodule Function

namespace GlobalTheory

namespace MaximalMinor

section Cramer

variable {A R F ι κ : Type*} [CommRing A] [CommRing R] [Algebra A R] [AddCommGroup F]
  [Module R F] [Module A F] [IsScalarTower A R F] [Fintype ι] [DecidableEq ι]

theorem det_smul_eq_sum_det_update (b : Basis ι R F) (v : ι → F) (x : F) :
    b.det v • x = ∑ i, b.det (update v i x) • v i := by
  apply b.equivFun.injective
  have h := Matrix.mulVec_cramer (b.toMatrix v) (b.equivFun x)
  rw [map_smul, Basis.det_apply, ← h]
  ext j

  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, Basis.equivFun_apply,
  smul_eq_mul, Matrix.mulVec, dotProduct, Matrix.cramer_apply, Basis.det_apply,
  Basis.toMatrix_update, Basis.toMatrix_apply, mul_comm]

theorem mem_span_of_det_update_mem (b : Basis ι R F) {v : ι → F}
    (hv : b.det v ∈ nonZeroDivisors R) {x : F}
    (hx : ∀ i, b.det (update v i x) ∈ span A {b.det v}) : x ∈ span A (Set.range v) := by
  choose a ha using fun i => mem_span_singleton.1 (hx i)
  refine (mem_span_range_iff_exists_fun A).2 ⟨a, ?_⟩
  have h1 : b.det v • (∑ i, a i • v i) = b.det v • x := by
    rw [det_smul_eq_sum_det_update b v x, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ha i, smul_assoc, ← algebraMap_smul R (a i), ← algebraMap_smul R (a i), smul_comm]
  apply b.equivFun.injective
  ext j
  have h2 := congrArg (fun y => b.equivFun y j) h1
  simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h2
  exact (mul_cancel_left_mem_nonZeroDivisors hv).1 h2

theorem span_range_comp_eq (b : Basis ι R F) (G : κ → F) {σ : ι → κ}
    (hσ : b.det (G ∘ σ) ∈ nonZeroDivisors R)
    (h : ∀ τ : ι → κ, b.det (G ∘ τ) ∈ span A {b.det (G ∘ σ)}) :
    span A (Set.range (G ∘ σ)) = span A (Set.range G) := by
  refine le_antisymm (span_mono (Set.range_comp_subset_range _ _)) (span_le.2 ?_)
  rintro _ ⟨k, rfl⟩
  refine mem_span_of_det_update_mem b hσ fun i => ?_
  rw [← comp_update]
  exact h _

end Cramer

end MaximalMinor

end GlobalTheory
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsAmpFramesExponents

section

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.AmpModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_ampFrames_of_cover (laws : Laws) {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω} {U₀ : M.Z.Opens}
    {EE : M.Lat S.J} (Z : ZHOut ρ M U₀ EE) (hU₀ : (U₀ : Set M.Z).Nonempty) {I : Type} (U : I → M.Z.Opens) (x : I → S.Gam)
    (b : I → Matrix S.J S.J Ω) (r : ℤ) (u : I → Ω) (hu : ∀ i, u i = S.th (x i) ^ (r + Fintype.card S.J) / (b i).det)
    (hcov : ∀ z, ∃ i, z ∈ U i) (haff : ∀ i, IsAffineOpen (U i)) (hne : ∀ i, (U i : Set M.Z).Nonempty)
    (hb : ∀ i, (b i).det ≠ 0)
    (hx : ∀ i, ∀ z ∈ U i, x i ∈ S.supI M z ∧ EE.E z = Submodule.span (M.O z) (Set.range (b i)))
    (hreg : ∀ i j, ∀ z ∈ U i, u j / u i ∈ M.O z) (hconv : ∀ i j, ∀ z ∈ U i, u i / u j ∈ M.O z → z ∈ U j) :
    ∃ A : LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  have h0 : ∀ i, S.th (x i) ≠ 0 := fun i => (hx i _ (hne i).some_mem).1.1
  obtain ⟨g, hLB, hamp, hg⟩ := exists_ample M U u hcov haff hne
    (fun i => by rw [hu]; exact div_ne_zero (zpow_ne_zero _ (h0 i)) (hb i)) hreg hconv
  choose σ hσ gσ nσ using fun i => Z.theta (U i) (x i) fun z hz => (hx i z hz).1
  choose τ hτ nτ using fun i => Z.sections (U i) (x i) (b i) (hx i)
  let e : Fin (Fintype.card S.J) ≃ S.J := (Fintype.equivFin S.J).symm
  refine ⟨⟨LB.mk I U g, hLB, hamp, Fintype.card S.J, fun i => secOver Z.G 1 (hσ i) _ (fun t => t.2),
    fun i k => secOver Z.G S.N (hτ i (e k)).1 _ (fun t => t.2), r, 1, fun i j => ?_, fun i V _ _ _ hV χ hχ => ?_⟩, rfl, rfl⟩
  · have n₂ : ((U i ⊓ U j : M.Z.Opens) : Set M.Z).Nonempty := M.nonempty_inf (hne i) (hne j)
    obtain ⟨c, hc⟩ := exists_unit M n₂ (div_ne_zero (h0 j) (h0 i)) (fun z hz => (hx i z hz.1).1.2 _)
      (fun z hz => by rw [inv_div]; exact (hx j z hz.2).1.2 _)
    have reg : ∀ i j, ∀ z ∈ U i, z ∈ U j → ∀ k k',
        (((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e) k k' ∈ M.O z := fun i j z hi hj k k' =>
      (M.O z).mul_mem ((hx i z hi).1.2 _) ((mem_span_rows_iff (M.O z) (hb j) (b i (e k))).1
        ((hx j z hj).2 ▸ (hx i z hi).2 ▸ Submodule.subset_span ⟨e k, rfl⟩) (e k'))
    obtain ⟨m, hm⟩ := exists_GL M n₂ (A := ((S.th (x j) / S.th (x i)) • (b i * (b j)⁻¹)).submatrix e e)
      (A' := ((S.th (x i) / S.th (x j)) • (b j * (b i)⁻¹)).submatrix e e) (by
        rw [Matrix.submatrix_mul_equiv, smul_mul_smul_comm, div_mul_div_cancel₀ (h0 i), div_self (h0 j), one_smul,
          Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (hb j).isUnit, Matrix.mul_nonsing_inv _ (hb i).isUnit,
          Matrix.submatrix_one_equiv])
      (fun z hz => reg i j z hz.1 hz.2) (fun z hz => reg j i z hz.2 hz.1)
    have one : valF M.pt (U i ⊓ U j) 1 = 1 := (M.res_apply _ n₂ 1).symm.trans (map_one _)
    refine ⟨Units.map (U i ⊓ U j).topIso.inv.hom.toMonoidHom c, Matrix.GeneralLinearGroup.map (U i ⊓ U j).topIso.inv.hom m,
      ⟨_, lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ i) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (gσ i) (fun _ => gσ i) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G 1 (hσ i) (fun _ : Fin 1 => hσ j) inf_le_left inf_le_right (fun _ => c.val)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (gσ i) (fun _ => gσ j) _ fun _ => by
            rw [Fin.sum_univ_one, ← M.res_apply _ n₂, hc, div_mul_eq_mul_div, mul_inv_cancel₀ (h0 j), one_div])
          _ _ (fun _ => rfl)⟩,
      fun k => ⟨_, lin_secOver Z.G S.N (hτ i (e k)).1 (fun _ : Fin 1 => (hτ i (e k)).1) inf_le_left inf_le_left (fun _ => 1)
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_left (hτ i (e k)).2 (fun _ => (hτ i (e k)).2) _ fun _ => by
            rw [Fin.sum_univ_one, one, _root_.one_mul]) _ _ (fun _ => (map_one _).symm),
        lin_secOver Z.G S.N (hτ i (e k)).1 (fun k' => (hτ j (e k')).1) inf_le_left inf_le_right (fun k' => m.val k k')
          (rel_of_genVal Z hU₀ _ _ inf_le_left inf_le_right (hτ i (e k)).2 (fun k' => (hτ j (e k')).2) _ fun l => ?_)
          _ _ (fun _ => rfl)⟩, ?_⟩
    · have v : ∀ k', valF M.pt (U i ⊓ U j) (m.val k k') = S.th (x j) / S.th (x i) * (b i * (b j)⁻¹) (e k) (e k') :=
        fun k' => (M.res_apply _ n₂ _).symm.trans (congrFun (congrFun hm k) k')
      have w : b i (e k) l = ∑ k', (b i * (b j)⁻¹) (e k) (e k') * b j (e k') l := by
        rw [e.sum_comp (fun a => (b i * (b j)⁻¹) (e k) a * b j a l), ← Matrix.mul_apply,
          Matrix.nonsing_inv_mul_cancel_right _ _ (hb j).isUnit]
      rw [w, Finset.sum_div]
      refine Finset.sum_congr rfl fun k' _ => ?_
      rw [v]
      have := h0 i
      have := h0 j
      field_simp
    · have key : g i j = c ^ r * Matrix.GeneralLinearGroup.det m := by
        refine Units.ext (M.res_injective _ n₂ ((hg i j).trans (Eq.symm ?_)))
        have e₁ : M.res _ n₂ (c ^ r).val = (S.th (x j) / S.th (x i)) ^ r := by
          rw [← hc]
          exact (congrArg Units.val (map_zpow (Units.map (M.res _ n₂).toMonoidHom) c r)).trans (Units.val_zpow_eq_zpow_val _ _)
        rw [Units.val_mul, map_mul, e₁, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det, hm,
          Matrix.det_submatrix_equiv_self, Matrix.det_smul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv',
          hu, hu, zpow_add₀ (h0 i), zpow_add₀ (h0 j), div_zpow, div_pow, zpow_natCast, zpow_natCast]
        have := h0 i
        have := h0 j
        have := hb i
        have := hb j
        field_simp
      show (U i ⊓ U j).topIso.inv.hom (g i j).val = _
      rw [key, zpow_one, Matrix.GeneralLinearGroup.map_det, ← map_zpow]
      exact map_mul _ _ _
  · let W₀ : M.Z.Opens := ⟨abLocus Z.G, by rw [Z.ab]; exact isOpen_TT_eq_bot S M⟩
    obtain ⟨ha, hk⟩ := Z.pol W₀ subset_rfl
    obtain ⟨A, φ, h₁, h₂, h₃⟩ := exists_polAV Z.G Z.semi S.g Z.dim Z.L Z.sym W₀ ha hk _ hχ
    have hr : ∀ {K : Type} [Field K] (y : Sp K ⟶ (U i).toScheme), Set.range (y ≫ (U i).ι) ⊆ U i := by
      rintro K _ y _ ⟨w, rfl⟩
      exact (y w).2
    refine ⟨GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L 1 1 (Over.mk (U i).ι) _ Z.L.isLB Z.semi le_rfl (fun K _ _ y c H => ?_) V hV χ A φ
        h₁ h₂ (one_pow _).symm,
      GlobalTheory.basisAlong_of_independent_fibres laws M.Z Z.G Z.L.L S.N _ (Over.mk (U i).ι) _ Z.L.isLB Z.semi (one_le_two.trans S.N_ge)
        (fun K _ _ y c H => ?_) V hV χ A φ h₁ h₂ (ρ.card.trans (by rw [h₃]))⟩
    · obtain ⟨p, j, hp, hne⟩ := nσ i K _ (hr y)
      have := indep_secOver Z.G 1 (fun _ : Fin 1 => hσ i) y c H p j hp
      rw [Fin.sum_univ_one] at this
      exact funext fun a => by rw [Subsingleton.elim a 0]; exact (mul_eq_zero.1 this).resolve_right hne
    · have := (nτ i K _ (hr y)).2 (c ∘ e.symm) fun p j hp => by
        rw [← e.sum_comp]
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using
          indep_secOver Z.G S.N (fun k => (hτ i (e k)).1) y c H p j hp
      exact funext fun a => by simpa using congrFun this (e a)

end GlobalTheory.AmpModel

namespace GlobalTheory

open AmpModel

theorem exists_ampFrames_exponents : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (n a : ℕ) (GG : Fin n → S.J → Ω) (Z : ZHOut ρ M U₀ EE), M.IsNm (fun q : S.Gam × (S.J → Fin n) => S.th q.1 * Matrix.det (Matrix.of fun i j => GG (q.2 i) j)) → S.Over₀ M U₀ → (∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => GG k j / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z) → ∃ r₀ : ℤ, ∀ r : ℤ, r₀ ≤ r → ∃ A : GlobalTheory.LN.AmpFrames Z.G Z.L.L S.N, A.r = r ∧ A.s = 1 := by
  intro laws o Ω _ _ _ _ S ρ M U₀ EE n a GG Z hN hO hdual
  let d : (S.J → Fin n) → Ω := fun k => Matrix.det (Matrix.of fun i j => GG (k i) j)
  let t : S.Gam × (S.J → Fin n) → Ω := fun q => S.th q.1 * d q.2
  refine ⟨1 + ((a : ℤ) - 1) * Fintype.card S.J, fun r hr => ?_⟩
  obtain ⟨e, rfl⟩ := Int.le.dest hr
  choose U haff hU _ using fun i : {q // t q ≠ 0} => hN.2 i.1 i.2
  have mem : ∀ i z, z ∈ U i ↔ M.Div t i.1 z := fun i z => Set.ext_iff.1 (hU i) z
  have h0 : ∀ i : {q // t q ≠ 0}, S.th i.1.1 ≠ 0 := fun i => left_ne_zero_of_mul i.2
  have hd : ∀ i : {q // t q ≠ 0}, d i.1.2 ≠ 0 := fun i => right_ne_zero_of_mul i.2
  have hth : ∀ i, ∀ z ∈ U i, i.1.1 ∈ S.supI M z := fun i z hz => ⟨h0 i, fun y => by
    have := ((mem i z).1 hz).2 (y, i.1.2)
    rwa [mul_div_mul_right _ _ (hd i)] at this⟩
  have hmin : ∀ i, ∀ z ∈ U i, ∀ k, d k / d i.1.2 ∈ M.O z := fun i z hz k => by
    have := ((mem i z).1 hz).2 (i.1.1, k)
    rwa [mul_div_mul_left _ _ (h0 i)] at this
  let B : {q // t q ≠ 0} → (S.J → Fin n) → Matrix S.J S.J Ω := fun i k => Matrix.of fun l j => GG (k l) j / S.th i.1.1 ^ a
  have hB : ∀ i k, (B i k).det = d k / (S.th i.1.1 ^ a) ^ Fintype.card S.J := fun i k => by
    have : B i k = (S.th i.1.1 ^ a)⁻¹ • Matrix.of fun l j => GG (k l) j := by
      ext l j
      simp [B, div_eq_inv_mul]
    rw [this, Matrix.det_smul, inv_pow, div_eq_inv_mul]
  have hB0 : ∀ i, (B i i.1.2).det ≠ 0 := fun i => by
    rw [hB]; exact div_ne_zero (hd i) (pow_ne_zero _ (pow_ne_zero _ (h0 i)))
  have hdet : ∀ i, ((B i i.1.2)⁻¹).transpose.det = (S.th i.1.1 ^ a) ^ Fintype.card S.J / d i.1.2 := fun i => by
    rw [Matrix.det_transpose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hB, inv_div]
  have ratio : ∀ i j : {q // t q ≠ 0}, t j.1 * S.th j.1.1 ^ e / (t i.1 * S.th i.1.1 ^ e) =
      t j.1 / t i.1 * (S.th j.1.1 / S.th i.1.1) ^ e := fun i j => by rw [div_pow, div_mul_div_comm]
  refine exists_ampFrames_of_cover laws Z hO.ne U (fun i => i.1.1) (fun i => ((B i i.1.2)⁻¹).transpose) _
    (fun i => t i.1 * S.th i.1.1 ^ e) (fun i => ?_) (fun z => ?_) haff
    (fun i => ⟨_, (mem i _).2 (RatModel.div_genericPoint i.2)⟩) (fun i => ?_) (fun i z hz => ⟨hth i z hz, ?_⟩)
    (fun i j z hz => ?_) (fun i j z hz h => ?_)
  · have : 1 + ((a : ℤ) - 1) * Fintype.card S.J + e + Fintype.card S.J = ((1 + e + a * Fintype.card S.J : ℕ) : ℤ) := by
      push_cast; ring
    rw [hdet, this, zpow_natCast]
    have := h0 i
    have := hd i
    simp only [t]
    field_simp
    ring
  · obtain ⟨q, hq⟩ := hN.1 z
    exact ⟨⟨q, hq.1⟩, (mem _ z).2 hq⟩
  · rw [hdet]; exact div_ne_zero (pow_ne_zero _ (pow_ne_zero _ (h0 i))) (hd i)
  · obtain ⟨V, b, hzV, hb, hE⟩ := EE.loc z
    rw [hE z hzV]
    refine eq_span_dual (M.O z) hb (hB0 i) fun w => ?_
    rw [← hE z hzV, ← hdual z _ (hth i z hz) w]
    have dd : ∀ k, (Pi.basisFun Ω S.J).det ((fun k j => GG k j / S.th i.1.1 ^ a) ∘ k) = (B i k).det := fun k => by
      rw [Module.Basis.det_apply, ← Matrix.det_transpose]
      congr 1
    have := MaximalMinor.span_range_comp_eq (A := M.O z) (Pi.basisFun Ω S.J) (fun k j => GG k j / S.th i.1.1 ^ a)
      (σ := i.1.2) (mem_nonZeroDivisors_of_ne_zero (by rw [dd]; exact hB0 i)) fun k => by
        rw [dd, dd, hB, hB]
        refine Submodule.mem_span_singleton.2 ⟨⟨_, hmin i z hz k⟩, ?_⟩
        have := hd i
        show d k / d i.1.2 * _ = _
        field_simp
    exact SetLike.ext_iff.1 this w
  · rw [ratio]
    exact (M.O z).mul_mem (((mem i z).1 hz).2 _) (pow_mem ((hth i z hz).2 _) _)
  · rw [ratio] at h
    refine (mem j z).2 ⟨j.2, fun q => ?_⟩
    have := (M.O z).mul_mem ((M.O z).mul_mem (((mem i z).1 hz).2 q) h) (pow_mem ((hth i z hz).2 j.1.1) e)
    convert this using 1
    have := h0 i
    have := h0 j
    have := i.2
    have := j.2
    rw [div_pow, div_pow]
    field_simp

end GlobalTheory
end
end
end
