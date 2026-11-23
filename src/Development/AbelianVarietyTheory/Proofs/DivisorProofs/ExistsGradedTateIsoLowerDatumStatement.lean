module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiltGraded
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionIsometryPrimitiveRootBijectiveModN
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueLineGen
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.RelationsAreFunctions
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueFamOfReps
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFrameRatio
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsThetaPow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentation
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffCommutatorPairingTorsion
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.AlphaPair
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- Source module: Development.AbelianVarietyTheory.Proofs.UniformizationProofs.WeilQkIsIffWeilIsAbelianPart

section

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.WeilAbelianPart

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem translPt_eq (b : TF (R := R) F ⟶ D.P.A) : translPt D.P.A b = DegPre.trPt D F b ≫ DegPre.prB D F :=
  (_root_.mul_comm (fst (TF (R := R) F) D.P.A ≫ b) (DegPre.prB D F)).trans (tr_pr D F b).symm

theorem translT_eq (b : TF (R := R) F ⟶ D.P.A) : translT D.P.A b = DegPre.trPt D F b := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [tr_fst, translT, lift_fst]
  · rw [translT, lift_snd, translPt_eq]

theorem exists_theta (hG : GlobalFnsSt) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) (w : Frm D F k p.g.b)
    (hw : w.IsGen) : ∃ θ : ThetaGrp D.P.A D.P.L (k : ℤ) (TF (R := R) F), θ.pt = p.g.b ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → ∀ (ρ : DegPre.BF D F ⟶ DegPre.BF D F) z J, Good D.P.L z J →
        sval (t.s 0) ρ.left z J = sval (s.s 0) (ρ ≫ DegPre.trPt D F p.g.b).left z J *
          (CommPairing.tval θ ρ.left z J).val := by
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_phi hG p w hw 0
  obtain ⟨v, hvg, hvv⟩ := exists_gen D.P.isLB (K' := Fin 2)
    (φ' := ![(snd (TF (R := R) F) D.P.A).left, (translPt D.P.A p.g.b).left])
    (ε' := ![(k : ℤ), -(k : ℤ)]) (fun U _ h => by
      have a := ThetaPow.prod_fam_zero D F k (fun q => h ((DegPre.trPt D F p.g.b).left ≫ q))
      have c : ∏ i, h (DegPre.famφ D F (0 + p.y) i) ^ DegPre.famε k i = h (DegPre.prB D F).left ^ k := by
        rw [hy, add_zero]; exact ThetaPow.prod_fam_zero D F k h
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ c (prod_neg _ _ a)) ?_
      rw [Fin.prod_univ_two, translPt_eq]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, zpow_natCast, Over.comp_left]) u hu
  refine ⟨⟨p.g.b, v, hvg⟩, rfl, fun s t H ρ z J hJ => ?_⟩
  have e := (phiRel_iff hG p w hw s t).1 H 0 0 (by rw [hy, add_zero]) _ ρ z J hJ
  rw [← hv u hu hc _ ρ z J hJ, ← hvv _ _ z J hJ] at e
  exact e

theorem eq_of_sval {k : ℕ} (s : Fam D F k) (hs : ¬ ∀ j, (s.s 0).f j = 0) {c c' : F}
    (h : ∀ y J, Good D.P.L y J → sval ((c • s).s 0) (𝟙 _) y J = sval ((c' • s).s 0) (𝟙 _) y J) : c = c' := by
  by_contra hne
  refine hs fun j => sec_ext_val (s' := SecOps.secZero) D.P.isLB (fun y J hJ => ?_) j
  have e : s = (c - c')⁻¹ • (c • s + (-1 : F) • c' • s) := by
    rw [neg_one_smul, ← sub_eq_add_neg, ← sub_smul, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hne), one_smul]
  have e₀ : c' • s + (-1 : F) • c' • s = 0 := by rw [neg_one_smul, add_neg_cancel]
  have e₁ := sval_add (c' • s) ((-1 : F) • c' • s) 0 (𝟙 _) y hJ
  rw [e₀, UUA.sval_zero_of (s := (0 : Fam D F k).s 0) (fun _ => rfl) _ y J (hJ.mem _ _)] at e₁
  rw [e, sval_smul _ _ _ _ y hJ, sval_add _ _ _ _ y hJ, h y J hJ, ← e₁, mul_zero,
    UUA.sval_zero_of (s := SecOps.secZero) (fun _ => rfl) _ y J (hJ.mem _ _)]

attribute [local instance] TorusExt.gtGroup in
theorem qkAdd_swap (hB : D.TauBimult) {k : ℕ} (p p' : QkPt D F k) : QkAdd p' p (TorusExt.qkAdd hB p p') := by
  have : TorusExt.qkAdd hB p p' = TorusExt.qkAdd hB p' p := TorusExt.qk_ext (add_comm _ _) (add_comm p.g p'.g)
  rw [this]
  exact TorusExt.qkAdd_qkAdd hB p' p

theorem weilQkIs_iff_weilIs_abelianPart : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (k : ℕ), 1 ≤ k → ∀ p p' : QkPt D.toPre F k, p.y = 0 → p'.y = 0 → ∀ ζ : Fˣ, WeilQkIs D.toPre F k p p' ζ ↔ WeilIs D.toPre.P.A D.toPre.P.L k p.g.b p'.g.b (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom ζ) := by
  intro hL R _ _ _ I hI D F _ _ _ k hk p p' hy hy' ζ
  have hG := hL.1.globalFns
  have hB := D.tau_bimult
  obtain ⟨Φ, h₁, -, h₃, -, h₅, -⟩ := PhiProj.phi_projective hL R I hI D F k hk
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F k p.g).1
  obtain ⟨w', hw'⟩ := (CoefBasic.coef_basic R D.toPre F k p'.g).1
  obtain ⟨v, hv, ev⟩ := h₅ p p' _ w w' hw hw' (TorusExt.qkAdd_qkAdd hB p p')
  obtain ⟨v', hv', ev'⟩ := h₅ p' p _ w' w hw' hw (qkAdd_swap hB p p')
  obtain ⟨c, -, hc⟩ := h₃ _ v' v hv' hv
  rw [ev, ev'] at hc
  have hc' : ∀ s, Φ p w (Φ p' w' s) = c • Φ p' w' (Φ p w s) := fun s => LinearMap.congr_fun hc s
  have r : ∀ s, PhiRel D.toPre F k p w s (Φ p w s) := fun s => ((h₁ p w hw).2 _ _).2 rfl
  have r' : ∀ s, PhiRel D.toPre F k p' w' s (Φ p' w' s) := fun s => ((h₁ p' w' hw').2 _ _).2 rfl
  obtain ⟨σ, hσ⟩ := FamFree.exists_sec_ne_zero (D := D.toPre) (F := F) hL.2.1.secTwist hk 0
  obtain ⟨t, rfl, -⟩ := FamFree.exists_fam_single hG hB hk 0 σ
  obtain ⟨t, rfl⟩ := (h₁ p' w' hw').1.2 t
  obtain ⟨s, rfl⟩ := (h₁ p w hw).1.2 t
  have key := weilQkIs_iff_of_comm hG D p p' w w' hw hw' c (fun s s₁ s₂ s₃ s₄ a₁ a₂ a₃ a₄ => by
    rw [((h₁ p w hw).2 _ _).1 a₂, ((h₁ p' w' hw').2 _ _).1 a₁, ((h₁ p' w' hw').2 _ _).1 a₄,
      ((h₁ p w hw).2 _ _).1 a₃, hc']) ⟨s, _, _, r s, r' _, fun h0 => hσ fun j => by rw [h0]; rfl⟩ hk (ζ : F)
  obtain ⟨θ, hp, hθ⟩ := exists_theta hG p hy w hw
  obtain ⟨θ', hp', hθ'⟩ := exists_theta hG p' hy' w' hw'
  obtain ⟨c₀, hc₀⟩ := CommutatorPairing.exists_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB θ θ'
  obtain ⟨z, rfl⟩ : ∃ z : Fˣ, unitOn z = c₀ :=
    ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom.toMonoidHom c₀, Units.ext (by simp [unitOn])⟩
  have hz := GlobalLift.weilIs_of_commIsOf hG D.toPre.P.isAb D.toPre.P.isLB hc₀
  rw [hp, hp'] at hz
  have hcz : c = (z : F) := eq_of_sval _ hσ fun y J hJ => by
    have e := congrArg Units.val ((CommPairing.commIsOf_iff D.toPre.P.isLB θ θ' _).1 hc₀ _ (𝟙 _) y J hJ)
    rw [Units.val_mul, Units.val_mul, Units.val_mul, ← gs_unit _ _ ⊤ trivial, hp, hp', translT_eq, translT_eq] at e
    have a₂ := hθ _ _ (r (Φ p' w' s)) (𝟙 _) y J hJ
    have a₁ := hθ' _ _ (r' s) (𝟙 _ ≫ DegPre.trPt D.toPre F p.g.b) y J hJ
    have a₄ := hθ' _ _ (r' (Φ p w s)) (𝟙 _) y J hJ
    have a₃ := hθ _ _ (r s) (𝟙 _ ≫ DegPre.trPt D.toPre F p'.g.b) y J hJ
    rw [a₁] at a₂
    rw [a₃] at a₄
    simp only [Category.id_comp, Over.id_left] at a₂ a₄ e
    rw [← hc', sval_smul _ _ _ _ y hJ, a₂, a₄, tr_comm, _root_.mul_assoc, _root_.mul_comm (Units.val _), e,
      Category.id_comp]
    show _ * (_ * _ * gs _ y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (z : F))) = _
    ring
  rw [key, hcz]
  constructor
  · intro H
    obtain rfl : ζ = z := Units.ext H
    exact hz
  · intro H
    exact congrArg Units.val (H1.unitOn_injective
      (CommutatorPairing.weilIs_unique hG D.toPre.P.isAb D.toPre.P.isLB H hz))

end GlobalTheory.UT.WeilAbelianPart
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatum

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.GradedTate

theorem exists_tateIso_of_perp {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H)
    (Z : Submodule (𝓞 E) Dw.La) (f : perp Dw Z →ₗ[𝓞 E] D'.La) (hf : IsLower Dw D' Z f) (K : Type) [Field K]
    (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → Kˣ → Prop) (ζ : ℕ → Kˣ)
    (hζ : ∀ n, 0 < n → IsPrimitiveRoot (ζ n) n) (hζ' : ∀ n m, 0 < n → 0 < m → ζ (n * m) ^ m = ζ n)
    (b : ℕ → perp Dw Z → Q) (hact : ∀ c, act c 1 = 1)
    (hcard : ∀ n, 0 < n → Nat.card {y : Q // y ^ n = 1} = n ^ Module.finrank ℤ D'.La)
    (huniq : ∀ n x y c c', e n x y c → e n x y c' → c = c')
    (hone : ∀ n y c, e n 1 y c → c = 1)
    (hadd : ∀ n, 0 < n → ∀ a a', b n (a + a') = b n a * b n a')
    (hlin : ∀ n, 0 < n → ∀ (c : 𝓞 E) a, b n (c • a) = act c (b n a))
    (hpow : ∀ n, 0 < n → ∀ a, b n a ^ n = 1)
    (htow : ∀ n m, 0 < n → 0 < m → ∀ a, b (n * m) a ^ m = b n a)
    (hiso : ∀ n, 0 < n → ∀ a a', e n (b n a) (b n a') (ζ n ^ Dw.EF a a')) :
    ∃ I' : TateIso D' K Q act e, (∀ n, I'.ζ n = ζ n) ∧ ∀ n, 0 < n → ∀ a, b n a = I'.ev n (f a) := by
  have := D'.proj
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf.1
  have hs' : ∀ w, f (s w) = w := fun w => LinearMap.congr_fun hs w
  have hiso' : ∀ n, 0 < n → ∀ a w', e n (b n a) (b n (s w')) (ζ n ^ D'.EF (f a) w') := fun n hn a w' => by
    have h := hiso n hn a (s w')
    rwa [← hf.2.2, hs'] at h
  have hiso'' : ∀ n, 0 < n → ∀ w w', e n (b n (s w)) (b n (s w')) (ζ n ^ D'.EF w w') := fun n hn w w' => by
    have h := hiso' n hn (s w) w'
    rwa [hs'] at h
  have hadd' : ∀ n, 0 < n → ∀ w w', b n (s (w + w')) = b n (s w) * b n (s w') := fun n hn w w' => by
    rw [map_add (f := _), hadd n hn]
  have hko := fun n (hn : 0 < n) => TorsIsometry.ker_and_onto E H D' K Q (e n) n (ζ n) (fun w => b n (s w)) hn
    (hcard n hn) (fun y c _ => hone n y c) (hζ n hn) (hadd' n hn) (fun w => hpow n hn _) (hiso'' n hn)
  refine ⟨{ ζ := ζ, ζ_prim := hζ, ζ_pow := hζ', ev := fun n w => if 0 < n then b n (s w) else 1
            add := fun n w w' => ?_, lin := fun n c w => ?_, ker := fun n hn => ?_, onto := fun n hn => ?_
            tower := fun n m hn hm w => ?_, isom := fun n hn w w' => ?_ }, fun _ => rfl, fun n hn a => ?_⟩
  · split_ifs with hn
    · exact hadd' n hn w w'
    · exact (_root_.mul_one _).symm
  · split_ifs with hn
    · rw [map_smul, hlin n hn]
    · exact (hact c).symm
  · simp only [if_pos hn]
    exact (hko n hn).1
  · simp only [if_pos hn]
    exact (hko n hn).2
  · simp only [if_pos hn, if_pos (Nat.mul_pos hn hm)]
    exact htow n m hn hm _
  · simp only [if_pos hn]
    exact hiso'' n hn w w'
  · show _ = if 0 < n then b n (s (f a)) else 1
    rw [if_pos hn]
    obtain ⟨w, hw⟩ := ((hko n hn).2 _).1 (hpow n hn a)
    obtain ⟨c, hc⟩ := TorsIsometry.exists_eq_nsmul_of_dvd D'.EF D'.unimod n (f a - w) fun w' => by
      have h₁ := hiso' n hn a w'
      rw [← hw] at h₁
      have h₂ := huniq _ _ _ _ _ h₁ (hiso'' n hn w w')
      rw [map_sub, LinearMap.sub_apply, ← (hζ n hn).zpow_eq_one_iff_dvd, zpow_sub, h₂, mul_inv_cancel]
    have h₃ : b n (s (f a - w)) = 1 := ((hko n hn).1 _).2 ⟨c, hc⟩
    have h₄ := hadd' n hn (f a - w) w
    rw [sub_add_cancel, h₃, _root_.one_mul] at h₄
    exact hw.symm.trans h₄.symm

section Pairs

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

attribute [local instance] TorusExt.gtGroup

theorem eq_of_equiv (hB : D.TauBimult) {k : ℕ} (hk : 0 < k) {p q : QkPt D F k} (h : QkPt.Equiv D F p q)
    (hy : p.y = q.y) : p = q := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 h
  have hz : k • z = 0 := by
    rw [hy] at h₁
    exact left_eq_add.1 h₁
  have : z = 0 := by
    rw [← natCast_zsmul] at hz
    exact (smul_eq_zero.1 hz).resolve_left (Int.natCast_ne_zero.2 hk.ne')
  subst this
  rw [map_zero, add_zero] at h₂
  exact TorusExt.qk_ext hy h₂.symm

theorem b_pow (hB : D.TauBimult) {k : ℕ} (p : QkPt D F k) (hy : p.y = 0) : p.g.b ^ k = 1 := by
  rw [← TorusExt.nsmul_b, TorusExt.qk_nsmul hB, hy, map_zero, TorusExt.zero_b]

theorem b_tower (hB : D.TauBimult) {n m : ℕ} (hn : 0 < n) {p p₀ : QkPt D F (n * m)} {q r r₀ : QkPt D F n}
    (hp : QkPt.Equiv D F p p₀) (hp₀ : p₀.y = 0) (hq : q.y = p.y) (hg : GtPtF.IsNsmul m p.g q.g)
    (hr : QkPt.Equiv D F q r) (hr' : QkPt.Equiv D F r r₀) (hr₀ : r₀.y = 0) : p₀.g.b ^ m = r₀.g.b := by
  obtain ⟨z, h₁, h₂⟩ := (TorusExt.equiv_iff hB _ _).1 hp
  have h₃ : TorusExt.qkShift hB q (m • z) = r₀ := by
    refine eq_of_equiv hB hn (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB (TorusExt.equiv_qkShift hB q _))
      (TorusExt.equiv_trans hB hr hr')) ?_
    show q.y + n • m • z = r₀.y
    rw [hr₀, hq, smul_smul, ← h₁, hp₀]
  rw [← h₃, ← TorusExt.nsmul_b, h₂, nsmul_add, ← (TorusExt.isNsmul_iff_eq _ _ _).1 hg, ← map_nsmul]
  rfl

end Pairs


attribute [local instance] TorusExt.gtGroup in
theorem exists_gradedTateIso : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  intro E _ _ _ H Dw D' Z f hf R _ _ _ hR t P F _ _ _ hrk I hI
  letI := H.starRing
  have hB := P.D.tau_bimult
  have hL := GlobalTheory.firstFiveLaws
  have hG := hL.1.globalFns
  have := hR.2
  have := hR.1.1
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  choose q hq hy using hI
  have huniq : ∀ (n : ℕ) (x y : TF (R := R) F ⟶ P.D.toPre.P.A) (c c' : Fˣ),
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c) →
      Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n x y (unitOn c') → c = c' := fun n x y c c' =>
    weilIs_unique_fieldPoint _ _ _ P.D.toPre.P.isLB F _ n x y c c'
  obtain ⟨I', h₁, h₂⟩ := exists_tateIso_of_perp Dw D' Z f hf F (TF (R := R) F ⟶ P.D.toPre.P.A)
    (fun a g => g ≫ P.oD.onB.act a)
    (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)) I.ζ I.ζ_prim I.ζ_pow
    (fun n a => if hn : 0 < n then (q n hn a).g.b else 1)
    (fun c => by
      have := P.oD.onB.hom c
      exact MonObj.one_comp _)
    (fun n hn => by
      have : NeZero n := ⟨hn.ne'⟩
      rw [hrk]
      exact (hL.1.mulN _ P.D.toPre.P n hn).2.2.2.2 F _
        (IsPrimitiveRoot.coe_units_iff.2 (I.ζ_prim n hn)).neZero'.ne)
    huniq
    (fun n y c h => by
      have h₁ := (hL.1.weil _ P.D.toPre.P n _).2.1 _ _ _ _ _ h h
      rw [_root_.mul_one] at h₁
      have e : unitOn (c * c) = unitOn c * unitOn c := map_mul _ _ _
      exact mul_eq_left.1 (huniq n 1 y _ _ (e ▸ h₁) h))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAdd_iff hB _ _ _).1
        ((TorusExt.qkAdd_iff_of_equiv hB (hq n hn a) (hq n hn a') (I.add n hn a a')).2 (hq n hn (a + a')))
      rw [← eq_of_equiv hB hn h (by
        show (q n hn a).y + (q n hn a').y = _
        rw [hy, hy, hy, add_zero])]
      exact TorusExt.add_b _ _)
    (fun n hn c a => by
      simp only [dif_pos hn]
      have h := (TorusExt.qkAct_iff hB hG P.oD _ _ _).1
        ((TorusExt.qkAct_iff_of_equiv hB hG P.oD (hq n hn a) (I.lin n hn c a)).2 (hq n hn (c • a)))
      rw [← eq_of_equiv hB hn h (by
        show c • (q n hn a).y = _
        rw [hy, hy, smul_zero])]
      exact TorusExt.gtSmul_b hG P.oD _ _)
    (fun n hn a => by
      simp only [dif_pos hn]
      exact b_pow hB _ (hy n hn a))
    (fun n m hn hm a => by
      simp only [dif_pos hn, dif_pos (Nat.mul_pos hn hm)]
      obtain ⟨r, r₁, r₂, r₃⟩ := I.tower n m hn hm a
      exact b_tower hB hn (hq _ _ a) (hy _ _ a) r₁ r₂ r₃ (hq n hn a) (hy n hn a))
    (fun n hn a a' => by
      simp only [dif_pos hn]
      exact (UT.WeilAbelianPart.weilQkIs_iff_weilIs_abelianPart hL R _ hR.1 P.D F n hn _ _ (hy n hn a) (hy n hn a')
        _).1 (PhiOperatorCompare.weilQkIs_of_equiv hB (hq n hn a) (hq n hn a') (I.isom n hn a a')))
  refine ⟨I', h₁, fun n hn a r hr hr₀ => ?_⟩
  rw [← h₂ n hn a, dif_pos hn, eq_of_equiv hB hn
    (TorusExt.equiv_trans hB (TorusExt.equiv_symm hB hr) (hq n hn a)) (hr₀.trans (hy n hn a).symm)]

end GlobalTheory.LowDat.GradedTate
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGradedTateIsoLowerDatumStatement

section

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory


theorem _root_.GlobalTheory.T.exists_gradedTateIso_lowerDatum : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (Dw D' : Datum H) (Z : Submodule (𝓞 E) Dw.La)
  (f : GlobalTheory.LowDat.perp Dw Z →ₗ[𝓞 E] D'.La), GlobalTheory.LowDat.IsLower Dw D' Z f →
  ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F],
  Module.finrank ℤ D'.La = 2 * P.D.toPre.P.g →
  ∀ I : (letI := H.starRing; TateIsoQ Dw P.D.toPre P.oD F),
  (∀ n, 0 < n → ∀ a : GlobalTheory.LowDat.perp Dw Z, ∃ q : QkPt P.D.toPre F n, QkPt.Equiv P.D.toPre F (I.ev n a) q ∧ q.y = 0) →
  ∃ I' : TateIso D' F (TF (R := R) F ⟶ P.D.toPre.P.A) (fun a g => g ≫ (letI := H.starRing; P.oD.onB.act a))
      (fun n g g' z => Out.WeilIs P.D.toPre.P.A P.D.toPre.P.L n g g' (unitOn z)),
    (∀ n, I'.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ (a : GlobalTheory.LowDat.perp Dw Z) (q : QkPt P.D.toPre F n),
      QkPt.Equiv P.D.toPre F (I.ev n a) q → q.y = 0 → q.g.b = I'.ev n (f a) := by
  first | exact @GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | exact GlobalTheory.LowDat.GradedTate.exists_gradedTateIso | (intros; apply GlobalTheory.LowDat.GradedTate.exists_gradedTateIso <;> assumption)
end
end
end
