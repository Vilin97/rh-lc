module

public import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
public import Mathlib.Tactic.ENatToNat
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
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
import Mathlib.RingTheory.Radical.NatInt
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorusCoordAdd

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenOfIso

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

section General
variable {X X' W Y Y₂ : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem exists_gen_of_iso (hL : L.IsLB) (hL' : L'.IsLB) {F : W ⟶ X} {F' : W ⟶ X'}
    (w : LB.Iso (L'.pull F') (L.pull F)) (hw : w.IsGen) (y : K → (Y ⟶ W)) (h : Y ⟶ Y₂) {φ : K → (Y₂ ⟶ X)}
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (ha : ∀ k, y k ≫ F' = φ' k) (hb : ∀ k, y k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J) (J'), Good L z J →
      Good L' z J' → val t (r ≫ h) z J =
        (∏ k, gw w (r ≫ y k) z (J ((r ≫ y k) ≫ F)) (fun _ => J' ((r ≫ y k) ≫ F')) ^ ε k) * val a r z J' := by
  obtain rfl : (fun k => y k ≫ F') = φ' := funext ha
  obtain ⟨a, ga, H⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hw) hL (pull_isLB hL' F') (φ' := y) h hb t ht
  have le : ∀ j : K → L'.ι, LB.wchart L' (fun k => y k ≫ F') j ≤ LB.wchart (L'.pull F') y (fun k _ => j k) :=
    fun j p hp => Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hp k)
  refine ⟨⟨fun j => res (le j) (a.s fun k _ => j k)⟩, isGen_of_gm _ fun p j j' hj hj' => ?_,
    fun Z r z J J' hJ hJ' => ?_⟩
  · refine (gm_res _ p (le j) hj _).trans ((gen_trans ga (𝟙 Y) p (le j hj) (le j' hj')).trans
      (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_) (gm_res _ p (le j') hj' _).symm))
    refine (gm_pull_g L' F' (𝟙 Y ≫ y k) p _ _ (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans ?_
    rw [Category.assoc]
  · have g' : Good (L'.pull F') z (fun ψ _ => J' (ψ ≫ F')) := fun ψ => mem_pull.2 (hJ' (ψ ≫ F'))
    refine (CubTransport.val_pmaps hb H r hJ g').trans (congrArg (_ * ·) ?_)
    rw [val_of _ r z J' (fun k => J' ((r ≫ y k) ≫ F')) (fun k => by rw [Category.assoc])]
    exact (gm_res r z (le _) (Set.mem_iInter.2 fun k => hJ' ((r ≫ y k) ≫ F')) _).symm

theorem exists_unit_base {S₀ : Scheme.{0}} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (a : Γ(Y, ⊤)ˣ) :
    ∃ c : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), gm r z ⊤ a = gm (r ≫ p) z ⊤ c := by
  obtain ⟨c, hc⟩ := hp a.val
  have e₁ : e.appTop.hom a.val = c := by
    rw [← hc, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, he]; simp
  refine ⟨Units.map e.appTop.hom.toMonoidHom a, fun Z r z => ?_⟩
  refine Eq.trans (congrArg (gm r z ⊤) (Units.ext ?_)) (gm_pull r p z ⊤ trivial _)
  exact hc.symm.trans (congrArg p.appTop.hom e₁.symm)

theorem surj_fst (hG : GlobalFnsSt) {S : Scheme.{0}} {A : Over S} [GrpObj A] (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (β_ T A).hom.left ≫ (snd A T).left := by
    rw [← Over.comp_left, braiding_hom_snd]
  rw [e]
  have : IsIso (β_ T A).hom.left := inferInstanceAs (IsIso ((Over.forget _).map (β_ T A).hom))
  have : IsIso (β_ T A).hom.left.appTop := inferInstanceAs (IsIso ((β_ T A).hom.left.app ⊤))
  exact surj_comp (ConcreteCategory.bijective_of_isIso (β_ T A).hom.left.appTop).2 (surj_snd hG hA T)

def comb {M : LB Y} (a : Γ(Y, ⊤)) (s t : LB.Sec M) : LB.Sec M where
  f j := (Y.presheaf.map (homOfLE le_top).op).hom a * s.f j + t.f j
  compat i j := by
    have e : ∀ {V : Y.Opens} (h : M.U i ⊓ M.U j ≤ V), (Y.presheaf.map (homOfLE h).op).hom
        ((Y.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom a) = (Y.presheaf.map (homOfLE le_top).op).hom a :=
      fun h => by rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [map_add (f := _), map_add (f := _), map_mul, map_mul, e, e, s.compat i j, t.compat i j]
    ring

def zeroSec (M : LB Y) : LB.Sec M where
  f _ := 0
  compat i j := by rw [map_zero, map_zero, mul_zero]

theorem sval_zeroSec {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) :
    sval (zeroSec (LB.LinComb L φ ε)) r z J = 0 := by
  unfold sval gs
  split_ifs
  · exact (congrArg _ (map_zero _)).trans (map_zero _)
  · rfl

theorem gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R)) (r : Z ⟶ Y) (z : Z)
    (c : R) : gs r z ⊤ (scal p c) = gs (r ≫ p) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c) :=
  gs_pull r p z ⊤ trivial _

end General

theorem cubN_twist {A B C U : Type} [CommGroup A] [CommGroup B] [CommGroup C] [CommGroup U] (β : A →* B) (κ : A →* C)
    (W : A → U) {θ : B → B → B → U} {θ' : C → C → C → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) * W (a * b) * W (a * c) * W (b * c) * W 1 =
      W (a * b * c) * W a * W b * W c * θ' (κ a) (κ b) (κ c)) {N : ℕ} {m : A} (hm : m ^ N = 1) (y : A) :
    cubN θ N 1 (β m) (β y) * W (m * y) ^ N * W 1 ^ N = W y ^ N * W m ^ N * cubN θ' N 1 (κ m) (κ y) := by
  have key : ∀ n : ℕ, cubN θ n 1 (β m) (β y) * W (m ^ n) * W y * W (m * y) ^ n * W 1 ^ n =
      W (m ^ n * y) * W 1 * W y ^ n * W m ^ n * cubN θ' n 1 (κ m) (κ y) := by
    intro n
    induction n with
    | zero => simp [cubN, mul_comm]
    | succ n ih =>
      have c := h (m ^ n) m y
      simp only [cubN, Finset.prod_range_succ, _root_.one_mul, map_pow, ← pow_succ m] at ih c ⊢
      simp only [pow_succ (W _)]
      apply Additive.ofMul.injective
      have ih' := congrArg Additive.ofMul ih
      have c' := congrArg Additive.ofMul c
      simp only [ofMul_mul] at ih' c' ⊢
      linear_combination (norm := abel) ih' + c'
  have k := key N
  rw [hm, _root_.one_mul y] at k
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul k
  simp only [ofMul_mul] at k' ⊢
  linear_combination (norm := abel) k'

section Theta
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

theorem exists_thetaGen {T : Over S} (x : T ⟶ G) {N : ℕ} (hx : x ^ N = 1)
    (f : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)])) (hf : f.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![(N : ℤ), -(N : ℤ)]),
      t.IsGen ∧ ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L.L z J →
        val t (lift τ y).left z J = cubN (cubV c z J) N 1 (τ ≫ x) y * val f τ.left z J := by
  obtain ⟨n, hn, vn⟩ := exists_cubN c 1 (fst T G ≫ x) (snd T G) N
  have hm : (fst T G ≫ x) ^ N = 1 := by rw [← MonObj.comp_pow, hx, MonObj.comp_one]
  obtain ⟨t, ht, vt⟩ := exists_gen L.isLB (φ' := ![(snd T G).left, ((fst T G ≫ x) * snd T G).left])
    (ε' := ![(N : ℤ), -(N : ℤ)]) (fun U _ h => by
      have q : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
        congrArg (fun q : T ⊗ G ⟶ G => q.left) (MonObj.comp_one (M := G) (fst T G))
      have p : ∏ k : Fin 2, h ((fst T G).left ≫ ![(1 : T ⟶ G).left, x.left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h (1 : T ⊗ G ⟶ G).left ^ (N : ℤ) * h (fst T G ≫ x).left ^ (-(N : ℤ)) := by
        rw [Fin.prod_univ_two, ← q]; rfl
      refine (DVR.prod_sum₂ (K := Fin 8) (K' := Fin 2) (U := U) _ rfl p).trans ?_
      rw [hm]
      apply Additive.ofMul.injective
      simp [Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
      module)
    (LB.mulGen L.L _ _ _ _ n (LB.pullGen L.L _ _ f (fst T G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hn (DVR.pullGen_isGen _ _ _ _ hf _))
  refine ⟨t, ht, fun T' τ y z J hJ => ?_⟩
  refine (vt _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((vn T' _ z J hJ).trans ?_)
    ((val_pull hJ _ _ _).trans ?_)))
  · rw [MonObj.comp_one, lift_fst_assoc, lift_snd]
  · rw [← Over.comp_left, lift_fst]

end Theta

section ThetaSec
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem exists_translSec (hL : L.IsLB) {T : Over S} (x : T ⟶ G) {N : ℤ}
    (t : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, ((fst T G ≫ x) * snd T G).left] ![N, -N]))
    (ht : t.IsGen) (σ : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd (𝟙_ _) G).left) (fun _ => N))) :
    ∃ σ' : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => N)),
      ∀ (T' : Over S) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good L z J →
        sval σ' (lift τ y).left z J =
          sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J * (val t (lift τ y).left z J).val := by
  obtain ⟨σ', v⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => N) (fun U _ h => by
      have q : (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left ≫ (snd (𝟙_ _) G).left =
          ((fst T G ≫ x) * snd T G).left := by rw [← Over.comp_left, lift_snd]
      refine (DVR.prod_sum₂ (K := Fin 1) (K' := Fin 2) (U := U) _ (Fin.prod_univ_one _) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_one]
      show h (_ ≫ _) ^ N * (h (snd T G).left ^ N * h ((fst T G ≫ x) * snd T G).left ^ (-N)) = _
      rw [q, zpow_neg, mul_left_comm, mul_inv_cancel, _root_.mul_one])
    (pullMulSec σ (lift (toUnit (T ⊗ G)) ((fst T G ≫ x) * snd T G)).left t ht)
  refine ⟨σ', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end ThetaSec

section Base
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
open ReciprocityTheory.ChartRestriction.G.DVR

theorem prod_famT {T T' : Over (Spec (CommRingCat.of R))} (ρ : T' ⟶ T ⊗ D.P.A) (α : D.X) (k : ℕ) {U : Type}
    [CommGroup U] (h : (T'.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ famφT D T α i) ^ DegPre.famε k i =
      h (ρ ≫ snd _ _).left ^ ((k : ℤ) - 1) * h (cP D T' α * (ρ ≫ snd _ _)).left * (h (cP D T' α).left)⁻¹ *
        h (1 : T' ⟶ D.P.A).left := by
  have e₁ : ρ.left ≫ famφT D T α 1 = (cP D T' α * (ρ ≫ snd _ _)).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (snd _ _) (cP D _ α)).trans (by rw [comp_cP, mul_comm]))
  have e₂ : ρ.left ≫ famφT D T α 2 = (cP D T' α).left := congrArg (fun q => q.left) (comp_cP D ρ α)
  have e₃ : ρ.left ≫ famφT D T α 3 = (1 : T' ⟶ D.P.A).left :=
    congrArg (fun q : T' ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]; rfl

def fac {T T' : Over (Spec (CommRingCat.of R))} (g : GtPt D T) (N : ℕ)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)])) (α : D.X)
    (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J : (T'.left ⟶ D.P.A.left) → D.P.L.ι) :
    (T'.left.presheaf.stalk z)ˣ :=
  cubN (th D z J) N 1 (τ ≫ g.b) y * val w τ.left z J * val (g.s α) τ.left z J *
    (th D z J (cP D T' α) (τ ≫ g.b) y)⁻¹

theorem exists_translFam {T : Over (Spec (CommRingCat.of R))} (g : GtPt D T) {N : ℕ} (hb : g.b ^ N = 1)
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, g.b.left] ![(N : ℤ), -(N : ℤ)]))
    (hw : w.IsGen) (α : D.X) (f : SecBT D (𝟙_ _) N α) :
    ∃ f' : SecBT D T N α, ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval f' (lift τ y).left z J =
        sval f (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val := by
  obtain ⟨t, ht, vt⟩ := exists_thetaGen D.cub g.b hb w hw
  let a : T ⊗ D.P.A ⟶ D.P.A := cP D _ α
  let m : T ⊗ D.P.A ⟶ D.P.A := fst _ _ ≫ g.b
  let x : T ⊗ D.P.A ⟶ D.P.A := snd _ _
  let u := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ t (LB.pullGen D.P.L _ _ (g.s α) (fst T D.P.A).left))
    (LB.invGen D.P.L _ _ (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t (lift a (lift m x)).left))
  have hu : u.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ ht (pullGen_isGen _ _ _ _ (g.isGen α) _))
    (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ D.cub.isGen _))
  obtain ⟨f', v⟩ := exists_sec D.P.isLB (φ' := famφT D T α) (ε' := DegPre.famε N) (fun U _ h => by
      have p₁ := prod_cub a m x h
      have p₂ := FormalPoint.prod_gtφT (fst T D.P.A) g.b α h
      have p₃ := prod_famT (𝟙 (T ⊗ D.P.A)) α N h
      have p₄ := prod_famT (lift (toUnit (T ⊗ D.P.A)) (m * x)) α N h
      have p₅ : ∏ k : Fin 2, h (![x.left, (m * x).left] k) ^ (![(N : ℤ), -(N : ℤ)] k) =
          h x.left ^ (N : ℤ) * h (m * x).left ^ (-(N : ℤ)) := Fin.prod_univ_two _
      simp only [Over.id_left, Category.id_comp] at p₃
      rw [lift_snd, ← _root_.mul_assoc (cP D _ α)] at p₄
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := (Fin 2 ⊕ Fin 4) ⊕ thK) (U := U) _ p₄
        (prod_sum₂ (K := Fin 2 ⊕ Fin 4) (K' := thK) (U := U) _
          (prod_sum₂ (K := Fin 2) (K' := Fin 4) (U := U) _ p₅ p₂) (prod_neg _ _ p₁))) (Eq.trans ?_ p₃.symm)
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, a, m, x]
      module)
    (pullMulSec f (lift (toUnit (T ⊗ D.P.A)) (m * x)).left u hu)
  refine ⟨f', fun T' τ y z J hJ => (v _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  have e : val u (lift τ y).left z J = fac g N w α τ y z J := by
    refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      (vt T' τ y z J hJ) ((val_pull hJ _ _ _).trans ?_))) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_cub D.cub (lift τ y) hJ _ _ _).trans ?_))))
    · rw [← Over.comp_left, lift_fst]
    · rw [comp_cP, lift_fst_assoc, lift_snd]
  rw [e, ← Over.comp_left, comp_lift, MonObj.comp_mul, lift_fst_assoc, lift_snd, toUnit_unique (_ ≫ _) (toUnit T')]

end Base

end GlobalTheory.UU.Transl
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLevelPoint

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

noncomputable section
namespace GlobalTheory.UU.Transl

theorem exp_alg {A X : Type} [CommRing A] {N : ℕ} {Wy Wxy Wx W1 cG cB vf vw : Aˣ} {σ : A} (s : Finset X) {f : X → A}
    {ty txy g θ : X → Aˣ} (h₁ : cB * Wxy ^ N * W1 ^ N = Wy ^ N * Wx ^ N * cG) (h₂ : vw * Wx ^ N = W1 ^ N * vf)
    (h₃ : ∀ α, txy α * θ α = g α * ty α) (h₄ : Wxy.val ^ N * σ = ∑ α ∈ s, f α * (txy α).val) :
    Wy.val ^ N * (σ * (cG * vf).val) = ∑ α ∈ s, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val := by
  have key : cB * vw * Wxy ^ N = Wy ^ N * (cG * vf) := by
    apply mul_right_cancel (b := W1 ^ N)
    calc cB * vw * Wxy ^ N * W1 ^ N = vw * (cB * Wxy ^ N * W1 ^ N) := by ac_rfl
      _ = vw * (Wy ^ N * Wx ^ N * cG) := by rw [h₁]
      _ = Wy ^ N * cG * (vw * Wx ^ N) := by ac_rfl
      _ = Wy ^ N * cG * (W1 ^ N * vf) := by rw [h₂]
      _ = Wy ^ N * (cG * vf) * W1 ^ N := by ac_rfl
  have hα : ∀ α, (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val =
      (cB * vw).val * (f α * (txy α).val) := by
    intro α
    have ht : txy α = g α * ty α * (θ α)⁻¹ := eq_mul_inv_of_mul_eq (h₃ α)
    have hu : cB * vw * g α * (θ α)⁻¹ * ty α = cB * vw * txy α := by rw [ht]; ac_rfl
    calc (f α * (cB * vw * g α * (θ α)⁻¹).val) * (ty α).val
        = f α * (cB * vw * g α * (θ α)⁻¹ * ty α).val := by rw [Units.val_mul _ (ty α), _root_.mul_assoc]
      _ = f α * (cB * vw * txy α).val := by rw [hu]
      _ = (cB * vw).val * (f α * (txy α).val) := by rw [Units.val_mul _ (txy α)]; ring
  rw [Finset.sum_congr rfl (fun α _ => hα α), ← Finset.mul_sum, ← h₄]
  have hv := congrArg Units.val key
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at hv
  simp only [Units.val_mul]
  linear_combination (-σ) * hv

section Level
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  (U : PreU I D A G) {T : Over (Spec (CommRingCat.of R))}
open ReciprocityTheory.ChartRestriction.G.DVR

def wv (e : ℕ) {Z : Scheme.{0}} (z : Z) (JG : (Z ⟶ G.left) → U.P.L.L.ι) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (a : Z ⟶ (thickObj R I e G).left) : (Z.presheaf.stalk z)ˣ :=
  gw (U.w e) a z (J (a ≫ (U.gt e).pG.left)) (fun _ => JG (a ≫ (fstG I e G).left))

def upHom (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ G) :=
  MonoidHom.mk' (fun a => (Over.map (thick R I e)).map a ≫ fstG I e G) FormalPoint.map_mul_fstG

def imHom (e : ℕ) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (Z ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj Z ⟶ D.P.A) :=
  MonoidHom.mk' (TorusCoord.im (U.gt e)) (TorusCoord.im_mul (U.gt e))

def FrameRel (x : T ⟶ G) (b : T ⟶ D.P.A) (N : ℕ)
    (f : LB.Gen (LB.LinComb U.P.L.L (K := Fin 2) ![(1 : T ⟶ G).left, x.left] ![(N : ℤ), -(N : ℤ)]))
    (w : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![(1 : T ⟶ D.P.A).left, b.left] ![(N : ℤ), -(N : ℤ)])) : Prop :=
  ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ T.left) (o a : Z ⟶ (thickObj R I e G).left),
    o ≫ (fstG I e G).left = r ≫ (1 : T ⟶ G).left → a ≫ (fstG I e G).left = r ≫ x.left →
    ∀ (z : Z) (JG) (J), Good U.P.L.L z JG → Good D.P.L z J →
      val w r z J * wv U e z JG J a ^ N = wv U e z JG J o ^ N * val f r z JG

variable {U}

theorem exists_level_point {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1) {e : ℕ}
    {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (τ : (Over.map (thick R I e)).obj Z ⟶ T) :
    ∃ a : Z ⟶ thickObj R I e G, upHom I e G Z a = τ ≫ x ∧ imHom U e Z a = τ ≫ g.b ∧ a ^ N = 1 := by
  obtain ⟨a, ha⟩ := GlobalTheory.FormalPoint.exists_lift_fstG (τ ≫ x)
  have hup : upHom I e G Z a = τ ≫ x := ha
  have hleft : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := by
    have := congrArg CommaMorphism.left ha
    simpa using this
  refine ⟨a, hup, ?_, ?_⟩
  · show (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b
    ext1
    simpa using (hr e _ τ.left a.left hleft).1
  · apply GlobalTheory.FormalPoint.eq_of_map_fstG
    change upHom I e G Z (a ^ N) = upHom I e G Z 1
    rw [map_pow, map_one, hup, ← CategoryTheory.MonObj.comp_pow, hx, CategoryTheory.MonObj.comp_one]

theorem exists_over_point {e : ℕ} {Z : Scheme.{0}} (y₀ : Z ⟶ (thickObj R I e G).left) (rG : Z ⟶ (T ⊗ G).left)
    (rB : Z ⟶ (T ⊗ D.P.A).left) (e₁ : rG ≫ (snd T G).left = y₀ ≫ (fstG I e G).left)
    (e₂ : rB ≫ (snd T D.P.A).left = y₀ ≫ (U.gt e).pG.left) (e₃ : rB ≫ (fst T D.P.A).left = rG ≫ (fst T G).left) :
    ∃ τ : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T,
      rG = (lift τ (upHom I e G _ (Over.homMk y₀ rfl))).left ∧ rB = (lift τ (imHom U e _ (Over.homMk y₀ rfl))).left := by
  have h1 : (fst T G).left ≫ T.hom = (snd T G).left ≫ G.hom := by
    rw [Over.w (fst T G), Over.w (snd T G)]
  have h2 : (fstG I e G).left ≫ G.hom = (thickObj R I e G).hom ≫ thick R I e := Over.w (fstG I e G)
  have hw : (rG ≫ (fst T G).left) ≫ T.hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    simp only [Category.assoc]
    rw [h1, reassoc_of% e₁, h2]
  have hG : rG ≫ (T ⊗ G).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T G), ← Category.assoc]; exact hw
  have hB : rB ≫ (T ⊗ D.P.A).hom = (y₀ ≫ (thickObj R I e G).hom) ≫ thick R I e := by
    rw [← Over.w (fst T D.P.A), ← Category.assoc, e₃]; exact hw
  refine ⟨Over.homMk (rG ≫ (fst T G).left) hw, ?_, ?_⟩
  · have key : (Over.homMk rG hG : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ G) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simp
      · rw [lift_snd]
        show Over.homMk rG hG ≫ snd T G = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ fstG I e G
        ext1; simpa using e₁
    exact congrArg CommaMorphism.left key
  · have key : (Over.homMk rB hB : (Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ T ⊗ D.P.A) =
        lift (Over.homMk (rG ≫ (fst T G).left) hw) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) := by
      apply CartesianMonoidalCategory.hom_ext
      · rw [lift_fst]; ext1; simpa using e₃
      · rw [lift_snd]
        show Over.homMk rB hB ≫ snd T D.P.A = (Over.map (thick R I e)).map (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) ≫ (U.gt e).pG
        ext1; simpa using e₂
    exact congrArg CommaMorphism.left key

theorem expT_transl (hG : GlobalFnsSt) {x : T ⟶ G} {g : GtPt D T} (hr : U.Red x g) {N : ℕ} (hx : x ^ N = 1)
    {f₀ w} (hf : FrameRel U x g.b N f₀ w) {σ : U.SecGT (𝟙_ _) N} {σ' : U.SecGT T N}
    {f : ∀ α, SecBT D (𝟙_ _) N α} {f' : ∀ α, SecBT D T N α}
    (hσ : ∀ (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ G) (z : T'.left) (J), Good U.P.L.L z J →
      sval σ' (lift τ y).left z J = sval σ (lift (toUnit T') ((τ ≫ x) * y)).left z J *
        (cubN (cubV U.P.c z J) N 1 (τ ≫ x) y * val f₀ τ.left z J).val)
    (hf' : ∀ α (T' : Over (Spec (CommRingCat.of R))) (τ : T' ⟶ T) (y : T' ⟶ D.P.A) (z : T'.left) (J),
      Good D.P.L z J → sval (f' α) (lift τ y).left z J =
        sval (f α) (lift (toUnit T') ((τ ≫ g.b) * y)).left z J * (fac g N w α τ y z J).val)
    (h : U.ExpT (𝟙_ _) N σ f) : U.ExpT T N σ' f' := by
  intro e
  obtain ⟨s, hs⟩ := h e
  refine ⟨s, ?_⟩
  intro Z y₀ rG rB e₁ e₂ e₃ z JG J hJG hJ
  obtain ⟨τ, hτG, hτB⟩ := exists_over_point (U := U) y₀ rG rB e₁ e₂ e₃
  subst hτG hτB
  obtain ⟨a, ha₁, ha₂, ha₃⟩ := exists_level_point hr hx τ
  have hal : a.left ≫ (fstG I e G).left = τ.left ≫ x.left := congrArg CommaMorphism.left ha₁
  have hu : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      (τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ fstG I e G =
      upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₁]
  have hi : (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      (τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) := by
    rw [show (Over.map (thick R I e)).map (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) ≫ (U.gt e).pG =
      imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)) from rfl, map_mul, ha₂]
  have c₁ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hu).symm
  have c₂ := (congrArg CommaMorphism.left (lift_snd (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left hi).symm
  have c₃ := (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).trans
    (congrArg CommaMorphism.left (lift_fst (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)))).symm
  obtain ⟨hz, hsum⟩ := hs Z (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ x) * upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left
    (lift (toUnit ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) ((τ ≫ g.b) * imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))).left c₁ c₂ c₃ z JG J hJG hJ
  refine ⟨fun α hα => ?_, ?_⟩
  · rw [hf' α _ τ _ z J hJ, hz α hα, zero_mul]
  have hcube : ∀ p q u : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G,
      @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
        (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) *
          wv U e z JG J (p * q).left * wv U e z JG J (p * u).left * wv U e z JG J (q * u).left *
          wv U e z JG J (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left =
        wv U e z JG J (p * q * u).left * wv U e z JG J p.left * wv U e z JG J q.left * wv U e z JG J u.left *
          @id (Z.presheaf.stalk z)ˣ (cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) p) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) q)
            (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) u)) :=
    fun p q u => (U.w_vals e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) z JG J hJG hJ (fun q => wv U e z JG J q.left) (fun _ => rfl)).2.2 p q u
  have H1 := cubN_twist (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom))) (fun q => wv U e z JG J q.left)
    (θ := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) D.cub z J) (θ' := cubV (T := ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom)))) U.P.c z JG) hcube ha₃ (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)
  rw [ha₁, ha₂] at H1
  have h1o : (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left ≫ (fstG I e G).left = τ.left ≫ (1 : T ⟶ G).left := by
    have h1 : upHom I e G (Over.mk (y₀ ≫ (thickObj R I e G).hom)) 1 = τ ≫ (1 : T ⟶ G) := by rw [map_one, MonObj.comp_one]
    exact congrArg CommaMorphism.left h1
  have H2 := hf e Z τ.left (1 : (Over.mk (y₀ ≫ (thickObj R I e G).hom)) ⟶ thickObj R I e G).left a.left h1o hal z JG J hJG hJ
  have ha₂' : (Over.map (thick R I e)).map a ≫ (U.gt e).pG = τ ≫ g.b := ha₂
  have H3 : ∀ α, @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) (a * (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl)).left z J) *
      @id (Z.presheaf.stalk z)ˣ (th D z J (cP D ((Over.map (thick R I e)).obj (Over.mk (y₀ ≫ (thickObj R I e G).hom))) α) (τ ≫ g.b) (imHom U e (Over.mk (y₀ ≫ (thickObj R I e G).hom)) (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl))) =
      @id (Z.presheaf.stalk z)ˣ (val (g.s α) τ.left z J) * @id (Z.presheaf.stalk z)ˣ (val ((U.gt e).t α) y₀ z J) := by
    intro α
    have ht := torus_coord_add hG R I D e G (U.gt e) (Over.mk (y₀ ≫ (thickObj R I e G).hom)) a (Over.homMk (U := Over.mk (y₀ ≫ (thickObj R I e G).hom)) (V := thickObj R I e G) y₀ rfl) α z J hJ
    rw [ha₂'] at ht
    rw [← (hr e _ τ.left a.left hal).2 α z J hJ]
    exact ht
  rw [hσ _ τ _ z JG hJG]
  simp only [hf' _ _ τ _ z J hJ]
  exact exp_alg s H1 H2 H3 hsum

end Level

end GlobalTheory.UU.Transl
end
end
end
