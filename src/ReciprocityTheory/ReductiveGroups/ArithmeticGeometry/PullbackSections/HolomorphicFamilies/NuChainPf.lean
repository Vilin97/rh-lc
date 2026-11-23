module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NuChain
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
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtSt
import Mathlib.Data.Nat.Choose.Multinomial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtB
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Linter.Style
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.SectionScalarValuation
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtPf

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

def SecBDvdSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
    ValOver ϖ (FractionRing V) vK →
    ∀ (k : ℕ) (α : D.toPre.X)
      (E : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))),
      VGe D (FractionRing V) vK k α E 0 → ∀ (r : V), r ≠ 0 → ∀ (f : D.toPre.SecB k α),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) E (D.toPre.famφB α)
        (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left
        (scal (DegPre.BF D.toPre (FractionRing V)).hom r) →
      ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
        f.f j = constFn D.toPre.P.A.hom _ r * g

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ S, a i) = ∑ i ∈ S, gs f y U (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [gs, dif_pos h, map_sum]

theorem isUnit_gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (u : Γ(X, U)ˣ) (k : ℕ) :
    IsUnit (gs f y U (u.val ^ k)) := by
  simp only [gs, dif_pos h]
  exact ((u.isUnit.pow k).map _).map _

theorem dvd_of_eq_sum {P : Scheme.{0}} {x : P} {W : P.Opens} (hmem : x ∈ W) {κ : Type} {S : Finset κ}
    {a b : κ → Γ(P, W)} {L : Γ(P, W)} (c : P.presheaf.stalk x) (heq : L = ∑ i ∈ S, a i * b i)
    (h : ∀ i ∈ S, c ∣ gs (𝟙 P) x W (a i)) : c ∣ gs (𝟙 P) x W L := by
  have hx : (𝟙 P) x ∈ W := by first | exact hmem | simpa using hmem
  subst heq
  rw [gs_fsum (𝟙 P) x W hx]
  refine Finset.dvd_sum fun i hi => ?_
  have hm : gs (𝟙 P) x W (a i * b i) = gs (𝟙 P) x W (a i) * gs (𝟙 P) x W (b i) := by
    simp only [gs, dif_pos hx, map_mul]
  rw [hm]
  exact (h i hi).mul_right _

theorem nuExt_of (hB : SecBDvdSt) : NuExtSt := by
  intro V _ _ _ ϖ hϖ D Q hQ vK hv A G _ _ _ _ _ U k hk s E hexp hnu
  obtain ⟨r, hr0, σ, f, hsσ, hEf, hexpAt⟩ := hexp
  have hvge : ∀ α, VGe D (FractionRing V) vK k α (E.s α) 0 :=
    n1e V ϖ hϖ D Q hQ (FractionRing V) vK k E hnu
  have hfd : ∀ α j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      (f α).f j = constFn D.toPre.P.A.hom _ r * g :=
    fun α => hB V ϖ hϖ D vK hv k α (E.s α) (hvge α) r hr0 (f α) (hEf α)
  choose g hg using hfd
  obtain ⟨n, hn⟩ := exists_pow_le_span hϖ hr0
  have hpw : (U.gt n).pG.left ≫ D.toPre.P.A.hom =
      pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom :=
    (Over.w (U.gt n).pG).trans pullback.condition.symm
  have hpt : ∀ (j : Fin 1 → U.LG.L.ι) (x' : ↑(pullback G.hom (thick V (maximalIdeal V) n))),
      pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j →
      cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r ∣
        gs (pullback.fst G.hom (thick V (maximalIdeal V) n)) x' (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)
          (σ.f j) := by
    intro j x' hx'
    obtain ⟨S, -, hS⟩ := hexpAt n
    obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB x' (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => J (U.gt n).pG.left, fun _ => j 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J ((U.gt n).pG.left ≫ D.toPre.famφB α i)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J (D.toPre.Oφ (U.gt n).pG α i)
    have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt n).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt n).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt n).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      rintro (a | a | a) (b | b | b) h <;> exact congrArg J h
    have hj0 : pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ U.LG.L.U (j 0) := Set.mem_iInter.1 hx' 0
    have hmem : x' ∈ U.expW n pp j S jf jt := by
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hJ _, Set.mem_iInter.2 fun _ => hj0⟩, hx'⟩, ?_⟩
      refine Finset.inf_induction (p := fun O : (thickObj V (maximalIdeal V) n G).left.Opens => x' ∈ O) trivial
        (fun a ha b hb => ⟨ha, hb⟩) (fun α _ => ⟨Set.mem_iInter.2 fun i => hJ _, Set.mem_iInter.2 fun i => hJ _⟩)
    have heq := hS pp j jf jt rfl hcoh

    have hterm : ∀ α ∈ S, ∀ (h : U.expW n pp j S jf jt ≤ (U.gt n).pG.left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)),
        gs (𝟙 _) x' (U.expW n pp j S jf jt) (((thickObj V (maximalIdeal V) n G).left.presheaf.map
          (homOfLE h).op).hom (((U.gt n).pG.left.app _).hom ((f α).f (jf α)))) =
        cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r *
          (show (pullback G.hom (thick V (maximalIdeal V) n)).presheaf.stalk x' from
            gs (U.gt n).pG.left x' _ (g α (jf α))) := by
      intro α _ h
      have hxα : (U.gt n).pG.left x' ∈ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) := h hmem
      exact (gs_res (𝟙 _) x' h hmem _).trans ((gs_pull (𝟙 _) (U.gt n).pG.left x' _ hxα _).trans
        ((congrArg (fun q => gs q x' _ ((f α).f (jf α))) (Category.id_comp _)).trans
          ((congrArg (gs (U.gt n).pG.left x' _) (hg α (jf α))).trans ((gs_mul _ x' _ hxα _ _).trans
            (congrArg (· * _) ((gs_constFn D.toPre.P.A.hom _ _ x' hxα r).trans
              (congrArg (fun q => cst q x' r) hpw)))))))
    have hdv := dvd_of_eq_sum hmem (cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r) heq
      (fun α _ => (dvd_mul_right _ _).trans (dvd_of_eq (hterm α.1 α.2 _).symm))
    have hdv2 := hdv.trans (dvd_of_eq (gs_mul (𝟙 _) x' _ hmem _ _))
    have hdv3 := (IsUnit.dvd_mul_left (isUnit_gs_pow (𝟙 _) x' _ hmem _ k)).1 hdv2
    exact hdv3.trans (dvd_of_eq ((gs_res (𝟙 _) x' _ hmem _).trans ((gs_pull (𝟙 _) _ x' _ hx' _).trans
      (congrArg (fun q => gs q x' _ (σ.f j)) (Category.id_comp _)))))
  obtain ⟨σ', hσ'⟩ := exists_div_sec_of_thick G.hom (maximalIdeal V ^ (n + 1)) hr0 hn σ hpt
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have h1 := secScal_sval_c hsσ (𝟙 _) y hJ
  have hm := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ pullback.fst G.hom (jK V))
  have h2 : sval σ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r * sval σ' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J :=
    (congrArg (gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y _) (hσ' _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg (· * _) (gs_constFn G.hom _ _ y hm r)))
  have hjK : ∀ a : V, (jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) a) :=
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have hcu : IsUnit (scal (pullback.snd G.hom (jK V) ≫ jK V) r) := by
    show IsUnit ((pullback.snd G.hom (jK V)).appTop.hom ((jK V).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)))
    rw [hjK]
    have hne : algebraMap V (FractionRing V) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hr0
    exact ((isUnit_iff_ne_zero.2 hne).map _).map _
  have hceq : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r) =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r :=
    (gs_pull (𝟙 _) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans
      (congrArg (fun q => gs q y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r))
        (by rw [Category.id_comp, Category.id_comp, pullback.condition]))
  have hgu : IsUnit (gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r)) := by
    rw [gs_eq (𝟙 _) y ⊤ trivial]
    exact (hcu.map _).map _
  rw [hceq] at hgu
  have h3 := h2.symm.trans (h1.trans (congrArg (· * _) hceq))
  exact hgu.mul_left_cancel h3

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtDone

section

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR

theorem nuExt : NuExtSt :=
  nuExt_of fun _ _ _ _ _ hϖ _ _ hv _ _ _ hE _ hr f hf => secB_dvd_of_vge hϖ hv hE hr f hf

end ReciprocityTheory.ChartRestriction.G.DVR
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGenVal

section

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.DVR.TG

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}

lemma hasVal_mul {c d : FractionRing V} {n m : ℤ} (hc : HasVal ϖ c n) (hd : HasVal ϖ d m) (hϖ : Irreducible ϖ) :
    HasVal ϖ (c * d) (n + m) := by
  obtain ⟨u, hu⟩ := hc
  obtain ⟨w, hw⟩ := hd
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  refine ⟨u * w, ?_⟩
  rw [hu, hw, zpow_add₀ hπ, Units.val_mul, map_mul]
  ring


open scoped Classical in
def valE (hϖ : Irreducible ϖ) (c : FractionRing V) : ℤ :=
  if h : c = 0 then 0 else (hasVal_of_ne_zero hϖ h).choose

lemma hasVal_valE (hϖ : Irreducible ϖ) {c : FractionRing V} (hc : c ≠ 0) : HasVal ϖ c (valE hϖ c) := by
  unfold valE
  rw [dite_eq_right hc]
  exact (hasVal_of_ne_zero hϖ hc).choose_spec


open scoped Classical in
def vK (hϖ : Irreducible ϖ) : AddValuation (FractionRing V) (WithTop ℚ) :=
  AddValuation.of (fun c => if c = 0 then ⊤ else ((valE hϖ c : ℚ) : WithTop ℚ))
    (by simp)
    (by
      have h1 : HasVal ϖ (1 : FractionRing V) 0 := ⟨1, by simp⟩
      simp [hasVal_unique hϖ (hasVal_valE hϖ one_ne_zero) h1])
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
      have key : ∀ {a b : FractionRing V}, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → valE hϖ a ≤ valE hϖ b →
          valE hϖ a ≤ valE hϖ (a + b) := by
        intro a b ha hb hab hle
        have hva := hasVal_valE hϖ ha
        have hvb := hasVal_valE hϖ hb
        have hvab := hasVal_valE hϖ hab
        generalize valE hϖ a = na at hva hle ⊢
        generalize valE hϖ b = nb at hvb hle
        generalize valE hϖ (a + b) = nab at hvab ⊢
        obtain ⟨u, hu⟩ := hva
        obtain ⟨w, hw⟩ := hvb
        obtain ⟨d, hd⟩ : ∃ d : ℕ, nb = na + d := ⟨(nb - na).toNat, by omega⟩
        set r : V := (u : V) + ϖ ^ d * (w : V)
        have hab' : a + b = algebraMap V (FractionRing V) ϖ ^ na * algebraMap V (FractionRing V) r := by
          rw [hu, hw, hd, zpow_add₀ hπ, zpow_natCast]
          simp only [r, map_add (f := _), map_mul, map_pow]
          ring
        have hr : r ≠ 0 := by
          rintro h0
          apply hab
          rw [hab', h0, map_zero, mul_zero]
        obtain ⟨k, z, hz⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr hϖ
        have hv : HasVal ϖ (a + b) (na + k) :=
          ⟨z, by rw [hab', hz, zpow_add₀ hπ, zpow_natCast, map_mul, map_pow]; ring⟩
        rw [hasVal_unique hϖ hvab hv]
        omega
      rcases le_total (valE hϖ x) (valE hϖ y) with h | h
      · have := key hx hy hxy h
        exact min_le_of_left_le (by exact_mod_cast this)
      · have := key hy hx (by rwa [add_comm]) h
        rw [add_comm] at this
        exact min_le_of_right_le (by exact_mod_cast this))
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      have hxy : x * y ≠ 0 := mul_ne_zero hx hy
      simp only [hx, hy, hxy, if_false]
      rw [hasVal_unique hϖ (hasVal_valE hϖ hxy) (hasVal_mul (hasVal_valE hϖ hx) (hasVal_valE hϖ hy) hϖ)]
      push_cast
      rfl)

lemma valOver_vK (hϖ : Irreducible ϖ) : ValOver ϖ (FractionRing V) (vK hϖ) := by
  intro c n hc
  have hπ : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero
  have hc0 : c ≠ 0 := by
    obtain ⟨u, hu⟩ := hc
    rw [hu]
    refine mul_ne_zero (zpow_ne_zero _ hπ) ?_
    exact (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr u.ne_zero
  change vK hϖ c = _
  simp only [vK, AddValuation.of_apply, if_neg hc0]
  rw [hasVal_unique hϖ (hasVal_valE hϖ hc0) hc]

end ReciprocityTheory.ChartRestriction.G.DVR.TG
end
end
end

-- Source module: ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NuChainPf

section

@[expose] public section

set_option autoImplicit false


noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

theorem secScal_cast {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {Y : Scheme.{0}} (h : Y ⟶ G.left)
    (k : ℕ) {L1 L2 : RigLB G} (e : L1 = L2)
    (s1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => h) (fun _ => (k : ℤ))))
    (σ1 : LB.Sec (LB.LinComb L1.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))))
    (hs : GeneratorPullback.SecScal L1.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) s1 (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ1 h 1) :
    GeneratorPullback.SecScal L2.L (fun _ : Fin 1 => h) (fun _ => (k : ℤ)) (e ▸ s1) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ))
      (e ▸ σ1) h 1 := by
  subst e; exact hs

theorem nuReg : NuRegSt := by
  intro E _ _ _ H V _ _ _ _ _ t P _ ϖ hϖ Q hQ vK hvK tK m w _ k hk F hF
  obtain ⟨s, Ex, htie, hexp, hnu⟩ := hF
  haveI := t.semi.smooth
  haveI := t.semi.separated
  haveI := t.semi.quasiCompact
  obtain ⟨σ', hσ'⟩ := nuExt V ϖ hϖ P.D Q hQ vK hvK P.A t.G P.U k hk s Ex hexp hnu
  have hsc := secScal_cast (pullback.fst t.G.hom (Out.jK V)) k P.bundle s σ' hσ'
  refine ⟨P.bundle ▸ σ', fun Z r zp hzp z J J' hJ hJ' => ?_⟩
  have e1 := ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_sval hsc (r ≫ iotaK m) z hJ
  rw [Category.assoc, iotaK, pullback.lift_fst] at e1
  exact e1.trans (htie Z r zp hzp z J J' hJ hJ')

theorem zCast_trans {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k₁ k₂ k₃ : ℤ} (h : k₁ = k₂) (h' : k₂ = k₃)
    (F : LB.Sec (LPow A L k₁ T)) : zCast A h' (zCast A h F) = zCast A (h.trans h') F := by
  subst h; subst h'; rfl

theorem zCast_self {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {k : ℤ} (h : k = k)
    (F : LB.Sec (LPow A L k T)) : zCast A h F = F := rfl

theorem regUnif_of (hN : NuDataSt) (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := by
  intro E _ _ _ H V _ _ _ _ _ t P hTor θ _ M hMu tK m w hrig θK hθK t₀ F hVt
  obtain ⟨ϖ, Q, vK, hϖ, hQ, hvK⟩ := hN E H V t P
  obtain ⟨t', α₀, α, s₁, U, hok1, hok2, hα₀, hnorm, hαc, htw, hsym, hact⟩ := hVt
  have hM1 : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMu
    · exact h
  have n0 := hT E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig θ θK hθK
  have n0' : NuK P Q vK m w 1 (zCast tK.G Nat.cast_one.symm (zCast tK.G Nat.cast_one θK)) := by
    rw [zCast_trans, zCast_self]; exact n0
  have n1 := hM E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig M hM1 (zCast tK.G Nat.cast_one θK) α₀ α s₁ n0'
    hα₀ hnorm hαc htw
  have hk : 0 < M ^ 2 := pow_pos hM1 2
  have n2 := hF E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig ((M : ℤ) ^ 2) (M ^ 2) (natCast_sq M) hk s₁ F t' U n1
    (by first | exact hok1 | exact hok2) hsym hact
  exact nuReg E H V t P hTor ϖ hϖ Q hQ vK hvK tK m w hrig (M ^ 2) hk (zCast tK.G (natCast_sq M) F) n2

theorem nuData : NuDataSt := by
  intro E _ _ _ H V _ _ _ _ _ t P
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using fun χ => QForm.exists_QVal hϖ P.D χ
  exact ⟨ϖ, Q, TG.vK hϖ, hϖ, hQ, TG.valOver_vK hϖ⟩

theorem regUnif_of' (hT : ThetaNuSt) (hM : MulNuSt) (hF : FinNuSt) : RegUnifSt := regUnif_of nuData hT hM hF

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end
end
