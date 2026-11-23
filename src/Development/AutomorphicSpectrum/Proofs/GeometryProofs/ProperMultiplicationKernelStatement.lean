module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimitiveDerivationPairingStatement
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.KernelRankMultiplicationCharP
public import Development.WeilBound.CoreStatements.HodgeTatePoints.GermCompOneAssocOfConstantCoeffZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GermDJet
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DualNumber
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.VtUniq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsGenOfIsVBOne
public import Mathlib.LinearAlgebra.Matrix.Rank

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubscheme

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.KerGeom

open PositivityTheory.Xgn.JetKernelRank Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.GermD ReciprocityTheory.ChartRestriction.G.DVR TensorProduct Algebra.TensorProduct TrivSqZeroExt

local notation "hm" φ:max => Formalism.L2.Pj.homAt (𝟙 (Sp _)) φ

theorem ker_data (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)]
    (hs : ∀ a : 𝓞 E, star a = H.bar a) (k : Type) [Field k] [IsAlgClosed k] (t : SAB H (Sp k))
    (hpr : IsProper t.G.hom) (hK : Out.KTriv t.G t.PP.L) (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E)
    (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left)
    (hp : IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left) {r s : ℕ}
    (u : Fin s → Fin d → k) (v : Fin r → Fin d → k) (lu : LinearIndependent k u) (lv : LinearIndependent k v)
    (hu : ∀ j, (rho g.B a).mulVec (u j) = 0) (hv : ∀ i, (rho g.B (H.bar a)).mulVec (v i) = 0) :
    ∃ (κ : Ov k A ⟶ t.G), κ ≫ t.act.act a = 1 ∧
      (∀ (T : Over (Sp k)) (x : T ⟶ t.G), x ≫ t.act.act a = 1 → ∃! y : T ⟶ Ov k A, y ≫ κ = x) ∧
      ∃ (Δ : A →ₐ[k] A ⊗[k] A) (e : A →ₐ[k] k) (f : Fin r → A) (D : Fin s → A →ₗ[k] k),
        hm Δ ≫ κ = (hm (includeLeft : A →ₐ[k] A ⊗[k] A) ≫ κ) * (hm includeRight ≫ κ) ∧ hm e ≫ κ = 1 ∧
        (∀ i, Δ (f i) = f i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] f i) ∧ LinearIndependent k f ∧
        (∀ i x y, D i (x * y) = e x * D i y + D i x * e y) ∧ LinearIndependent k D ∧
        ∀ j i, D j (f i) = u j ⬝ᵥ (bil (g.B.ad a) 1 1).mulVec (v i) := by
  have hA := AbelianSchemeGerms.isAbelianScheme_of_proper t.G t.semi
  have := t.act.hom a
  have := t.act.hom (H.bar a)
  obtain ⟨κ, h₁, h₂⟩ := exists_ker i hp
  obtain ⟨w, hw, hU⟩ := g.frame.ad a
  obtain ⟨U, hU₁, hU₂⟩ := hU 3
  have hW : AdSum (t.act.act a) (t.act.act (H.bar a))
      (Sum.elim (cφG t ![fst t.G t.G, snd t.G t.G ≫ t.act.act (H.bar a)])
        (cφG t ![fst t.G t.G ≫ t.act.act a, snd t.G t.G])) (Sum.elim (cε 2) (fun I => -cε 2 I)) :=
    fun {T} p q U _ h => by
      refine (prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := U) _
        (prod_cube₂ _ _ fun r => h ((lift p q).left ≫ r))
        (prod_neg _ _ (prod_cube₂ _ _ fun r => h ((lift p q).left ≫ r)))).trans ?_
      simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst, lift_snd, lift_fst_assoc,
        lift_snd_assoc]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
  have cc : MvPowerSeries.constantCoeff (g.B.ad a) = 1 := by
    rw [← PositivityTheory.HtPt.Ca.cc_ev (a := ![0, Germ.pt k (n := 1) d 0]) (fun j i => by fin_cases j <;> simp [Germ.pt]),
      g.B.adjoint_zero_fst, map_one]
  have h11 : ∀ (R : Type) [CommRing R] [Algebra k R], Chi w (1 : Ov k R ⟶ t.G) 1 1 := fun R _ _ => by
    have h0 : ∀ i j : Fin d, (0 : Fin d → R) i * (0 : Fin d → R) j = 0 := by simp
    have := chi_chart g w a U hU₂ 0 0 h0 h0 (by simp) (by simp)
    obtain ⟨α, β, e⟩ := second_jet_expansion (k := k) 0 0 h0 h0 (g.B.ad a)
    rw [cp_zero g _ _ rfl, hU₁, e, cc] at this
    simpa using this
  have sq : ∀ {n : ℕ} (v : Fin n → Fin d → k) (i j : Fin d),
      (inr (fun l => v l i) : Sq k n) * inr (fun l => v l j) = 0 := fun v i j => inr_mul_inr _ _ _
  have kill : ∀ {n : ℕ} (v : Fin n → Fin d → k) (M : Matrix (Fin d) (Fin d) k), (∀ l, M.mulVec (v l) = 0) →
      ∀ j, ∑ i, M j i • (inr (fun l => v l i) : Sq k n) = 0 := fun v M h j => by
    refine TrivSqZeroExt.ext (by simp [fst_sum]) (funext fun l => ?_)
    simpa [snd_sum, Matrix.mulVec, dotProduct] using congrFun (h l) j
  have dirv : ∀ {n : ℕ} (v : Fin n → Fin d → k), LinearIndependent k v → ∀ l : Fin n → k,
      hm (dir l) ≫ cp g _ (sq v) = 1 → ∀ i, l i = 0 := fun v lv l h => by
    rw [cp_nat g _ _ _ (fun j => (inr ((∑ i, l i • v i) j) : DualNumber k)) (fun _ _ => inr_mul_inr _ _ _)
      (fun j => by simp [dir, dotProduct])] at h
    exact Fintype.linearIndependent_iff.1 lv l (cp_inj g hs _ _ h)
  let z : Ov k (Sq k r) ⟶ t.G := cp g _ (sq v)
  have hz : z ≫ t.act.act (H.bar a) = 1 := cp_act g _ _ _ (kill v _ hv)
  have ker : ∀ {T : Over (Sp k)} (y : T ⟶ Ov k A), (y ≫ κ) ≫ t.act.act a = 1 := fun y => by
    rw [Category.assoc, h₁, MonObj.comp_one]
  have ker' : ∀ {T : Over (Sp k)} (y : T ⟶ Ov k (Sq k r)), (y ≫ z) ≫ t.act.act (H.bar a) = 1 := fun y => by
    rw [Category.assoc, hz, MonObj.comp_one]
  obtain ⟨ψ, hψ⟩ := pt_surj h₂ (cp g _ (sq u)) (cp_act g _ _ _ (kill u _ hu))
  obtain ⟨e, he⟩ := pt_surj h₂ (1 : Ov k k ⟶ t.G) (MonObj.one_comp _)
  obtain ⟨Δ, hΔ⟩ := pt_surj h₂ ((hm (includeLeft : A →ₐ[k] A ⊗[k] A) ≫ κ) * (hm includeRight ≫ κ))
    (by rw [MonObj.mul_comp, ker, ker, _root_.mul_one])
  obtain ⟨c, hc⟩ := chi_exists hw hW (hm (includeLeft : A →ₐ[k] A ⊗[k] Sq k r) ≫ κ) (hm includeRight ≫ z)
    (ker _) (ker' _)
  have N : ∀ {B C : Type} [CommRing B] [Algebra k B] [CommRing C] [Algebra k C] (θ : A →ₐ[k] B) (ν : Sq k r →ₐ[k] C),
      Chi w (hm includeLeft ≫ hm θ ≫ κ) (hm includeRight ≫ hm ν ≫ z) (Algebra.TensorProduct.map θ ν c) :=
    fun θ ν => by
      have := hc.nat (Algebra.TensorProduct.map θ ν)
      rwa [← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp, map_comp_includeLeft, map_comp_includeRight,
        ← homAt_comp, ← homAt_comp, Category.assoc, Category.assoc] at this
  have c1 : c0 k r A c = 1 := by
    have := hc.nat (c0 k r A)
    rw [← Category.assoc (hm (c0 k r A)) (hm includeRight), homAt_comp,
      cp_nat g _ _ _ 0 (by simp) (fun j => by simp), cp_zero g _ _ rfl] at this
    exact this.unique (chi_one hA hw hW (h11 A) _).1
  have fψ : ∀ x, (ψ x).fst = e x := by
    have : (fstHom k k _).comp ψ = e := pt_inj h₁ h₂ (by
      rw [← homAt_comp, Category.assoc, hψ, he, cp_nat g _ _ _ 0 (by simp) (fun j => by simp), cp_zero g _ _ rfl])
    exact fun x => DFunLike.congr_fun this x
  refine ⟨κ, h₁, h₂, Δ, e, fun i => co i c, fun j => LinearMap.proj j ∘ₗ sndHom k _ ∘ₗ ψ.toLinearMap, hΔ, he,
    fun i => ?_, Fintype.linearIndependent_iff.2 fun l hl => ?_, fun j x y => ?_,
    Fintype.linearIndependent_iff.2 fun l hl => ?_, fun j i => ?_⟩
  · have a₁ := N Δ (AlgHom.id k _)
    rw [hΔ, MonObj.comp_mul] at a₁
    have a₂ := chi_mul hA hw hW (h11 _) (by rw [← Category.assoc]; exact ker _)
      (by rw [← Category.assoc]; exact ker' _) (N (includeLeft : A →ₐ[k] A ⊗[k] A) (AlgHom.id k _))
      (N (includeRight : A →ₐ[k] A ⊗[k] A) (AlgHom.id k _))
    rw [← co_map, a₁.unique a₂, co_mul, co_map, co_map, map_lineCoeffConst, map_lineCoeffConst, c1]
    simp [add_comm]
  · obtain ⟨_, _, _⟩ := flat_surj h₂ hA
    have a₁ := N (AlgHom.id k A) (dir l)
    rw [map_dir, hl, c1, zero_tmul, add_zero, ← Algebra.TensorProduct.one_def, homAt_id, Category.id_comp] at a₁
    refine dirv v lv l (pair_nondeg hA t.PP.isLB hw hW hK _ (hm (dir l) ≫ z) (ker' _) fun T ρ x hx y J hJ => ?_)
    obtain ⟨x, rfl, -⟩ := h₂ T x hx
    obtain ⟨τ, rfl, rfl⟩ := exists_tensor x ρ
    have a₂ := (a₁ T τ y J hJ).trans ((chi_one hA hw hW (h11 _)
      (hm (includeRight : DualNumber k →ₐ[k] A ⊗[k] DualNumber k) ≫ hm (dir l) ≫ z)).2 T τ y J hJ).symm
    rw [MonObj.comp_one] at a₂
    simpa only [Category.assoc] using Units.ext a₂
  · simp [snd_mul, fψ, mul_comm]
  · refine dirv u lu l ?_
    have : (dir l).comp ψ = (Algebra.ofId k _).comp e := AlgHom.ext fun x => by
      have := DFunLike.congr_fun hl x
      ext
      · simp [dir, fψ, algebraMap_eq_inl]
      · simpa [dir, dotProduct, algebraMap_eq_inl] using this
    rw [← hψ, ← Category.assoc, homAt_comp, this, ← homAt_comp, Category.assoc, he, MonObj.comp_one]
  · have a₁ := N ψ (AlgHom.id k _)
    let a' : Fin d → Sq k s ⊗[k] Sq k r := fun m => inr (fun l => u l m) ⊗ₜ 1
    let b' : Fin d → Sq k s ⊗[k] Sq k r := fun m => 1 ⊗ₜ inr (fun l => v l m)
    have ha : ∀ i j, a' i * a' j = 0 := fun i j => by simp [a']
    have hb : ∀ i j, b' i * b' j = 0 := fun i j => by simp [b']
    rw [hψ, homAt_id, Category.id_comp, cp_nat g _ _ _ a' ha (fun _ => rfl), cp_nat g _ _ _ b' hb (fun _ => rfl)] at a₁
    have a₂ := chi_chart g w a U hU₂ a' b' ha hb
      (fun m => by simpa [a', sum_tmul, smul_tmul'] using congrArg (· ⊗ₜ[k] (1 : Sq k r)) (kill u _ hu m))
      (fun m => by simpa [b', tmul_sum] using congrArg ((1 : Sq k s) ⊗ₜ[k] ·) (kill v _ hv m))
    obtain ⟨α, β, e'⟩ := second_jet_expansion (k := k) a' b' ha hb (g.B.ad a)
    have a₃ := congrArg (fun q => (co i q).snd j) ((a₁.unique a₂).trans ((congrArg _ hU₁).trans e'))
    simp only [co_map] at a₃
    refine a₃.trans ?_
    simp [a', b', snd_sum, Algebra.TensorProduct.algebraMap_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem assemble {k H : Type} [Field k] [CommRing H] [HopfAlgebra k H] {V V' : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] {r s : ℕ} (bV : Module.Basis (Fin r) k V') (bU : Module.Basis (Fin s) k V)
    (f : Fin r → H) (hf : ∀ i, Coalgebra.comul (R := k) (f i) = f i ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] f i)
    (hfi : LinearIndependent k f) (D₀ : Fin s → H →ₗ[k] k)
    (hD : ∀ i x y, D₀ i (x * y) = D₀ i x * Coalgebra.counit (R := k) y + Coalgebra.counit (R := k) x * D₀ i y)
    (hli : LinearIndependent k D₀) (P : V →ₗ[k] V' →ₗ[k] k) (hP : ∀ j i, D₀ j (f i) = P (bU j) (bV i)) :
    ∃ (D : V →ₗ[k] (H →ₗ[k] k)) (T : V' →ₗ[k] H), Function.Injective D ∧ Function.Injective T ∧
      (∀ u x y, D u (x * y) = D u x * Coalgebra.counit (R := k) y + Coalgebra.counit (R := k) x * D u y) ∧
      (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : H) + (1 : H) ⊗ₜ[k] T z) ∧
      ∀ u z, D u (T z) = P u z := by
  have inj : ∀ {W M : Type} [AddCommGroup W] [Module k W] [AddCommGroup M] [Module k M] {n : ℕ}
      (b : Module.Basis (Fin n) k W) (c : Fin n → M), LinearIndependent k c → Function.Injective (b.constr k c) := by
    intro W M _ _ _ _ n b c hc
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    rw [Module.Basis.constr_apply_fintype] at hx
    have h0 := Fintype.linearIndependent_iff.1 hc _ hx
    exact b.equivFun.injective (by ext i; simpa using h0 i)
  refine ⟨bU.constr k D₀, bV.constr k f, inj bU D₀ hli, inj bV f hfi, fun u x y => ?_, fun z => ?_, fun u z => ?_⟩
  · simp only [Module.Basis.constr_apply_fintype, LinearMap.sum_apply, LinearMap.smul_apply, hD, smul_eq_mul,
      mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun _ _ => by ring) (Finset.sum_congr rfl fun _ _ => by ring)

  · simp only [Module.Basis.constr_apply_fintype, map_sum, map_smul, hf, smul_add, Finset.sum_add_distrib,
    TensorProduct.sum_tmul, TensorProduct.tmul_sum, TensorProduct.smul_tmul', TensorProduct.tmul_smul]
  · conv_rhs => rw [← bU.sum_equivFun u, ← bV.sum_equivFun z]

    simp only [Module.Basis.constr_apply_fintype, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, hP]


open Algebra.TensorProduct in
theorem exists_hopf {k : Type} [Field k] {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {f : G ⟶ G} [IsMonHom f]
    {A : Type} [CommRing A] [Algebra k A] [Module.Finite k A] {κ : Ov k A ⟶ G} (h₁ : κ ≫ f = 1)
    (h₂ : ∀ (T : Over (Sp k)) (x : T ⟶ G), x ≫ f = 1 → ∃! y : T ⟶ Ov k A, y ≫ κ = x)
    (Δ : A →ₐ[k] A ⊗[k] A) (hΔ : hm Δ ≫ κ = (hm includeLeft ≫ κ) * (hm includeRight ≫ κ))
    (ε : A →ₐ[k] k) (hε : hm ε ≫ κ = 1) {V V' : Type} [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] {r s : ℕ} (bV : Module.Basis (Fin r) k V') (bU : Module.Basis (Fin s) k V)
    (u : Fin r → A) (hf : ∀ i, Δ (u i) = u i ⊗ₜ[k] 1 + 1 ⊗ₜ[k] u i) (hfi : LinearIndependent k u)
    (D₀ : Fin s → A →ₗ[k] k) (hD : ∀ i a b, D₀ i (a * b) = ε a * D₀ i b + D₀ i a * ε b)
    (hli : LinearIndependent k D₀) (P : V →ₗ[k] V' →ₗ[k] k) (hP : ∀ j i, D₀ j (u i) = P (bU j) (bV i)) :
    ∃ (A' : Type) (_ : CommRing A') (_ : HopfAlgebra k A') (_ : Coalgebra.IsCocomm k A') (_ : Module.Finite k A'),
      Module.finrank k A' = Module.finrank k A ∧
      ∃ (D : V →ₗ[k] (A' →ₗ[k] k)) (T : V' →ₗ[k] A'), Function.Injective D ∧ Function.Injective T ∧
        (∀ u x y, D u (x * y) = D u x * Coalgebra.counit (R := k) y + Coalgebra.counit (R := k) x * D u y) ∧
        (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : A') + (1 : A') ⊗ₜ[k] T z) ∧
        ∀ u z, D u (T z) = P u z := by
  obtain ⟨σ, hσ⟩ := pt_surj h₂ κ⁻¹ (by rw [GrpObj.inv_comp, h₁, inv_one])
  have mul : ∀ {R : Type} [CommRing R] [Algebra k R] (θ : A ⊗[k] A →ₐ[k] R), hm (θ.comp Δ) ≫ κ =
      (hm (θ.comp includeLeft) ≫ κ) * (hm (θ.comp includeRight) ≫ κ) := fun θ => by
    rw [← homAt_comp, Category.assoc, hΔ, MonObj.comp_mul, ← Category.assoc, ← Category.assoc, homAt_comp, homAt_comp]
  have one : ∀ {R : Type} [CommRing R] [Algebra k R] (θ : k →ₐ[k] R), hm (θ.comp ε) ≫ κ = 1 := fun θ => by
    rw [← homAt_comp, Category.assoc, hε, MonObj.comp_one]
  have hid : hm (AlgHom.id k A) ≫ κ = κ := by rw [homAt_id, Category.id_comp]
  have cg : ∀ {R : Type} [CommRing R] [Algebra k R] {φ ψ : A →ₐ[k] R}, φ = ψ → hm φ ≫ κ = hm ψ ≫ κ :=
    fun h => by rw [h]
  letI : Bialgebra k A := Bialgebra.ofAlgHom Δ ε
    (pt_inj h₁ h₂ (by
      let a := (Algebra.TensorProduct.assoc k k k A A A).toAlgHom
      have e₁ : (a.comp (Algebra.TensorProduct.map Δ (.id k A))).comp includeLeft =
        (a.comp includeLeft).comp Δ := by ext x; simp
      have e₂ : (Algebra.TensorProduct.map (.id k A) Δ).comp includeRight =
        (includeRight : A ⊗[k] A →ₐ[k] A ⊗[k] (A ⊗[k] A)).comp Δ := by ext x; simp
      rw [← AlgHom.comp_assoc, mul, mul, e₁, e₂, mul, mul, _root_.mul_assoc]
      exact congrArg₂ (· * ·) (cg (by ext x; simp [a, Algebra.TensorProduct.one_def])) (congrArg₂ (· * ·)
        (cg (by ext x; simp [a, Algebra.TensorProduct.one_def])) (cg (by ext x; simp [a, Algebra.TensorProduct.one_def])))))
    (pt_inj h₁ h₂ (by
      have e₁ : (Algebra.TensorProduct.map ε (.id k A)).comp includeLeft =
        (includeLeft : k →ₐ[k] k ⊗[k] A).comp ε := by ext x; simp
      rw [mul, e₁, one, _root_.one_mul]
      exact cg (by ext x; simp)))
    (pt_inj h₁ h₂ (by
      have e₁ : (Algebra.TensorProduct.map (.id k A) ε).comp includeRight =
        (includeRight : k →ₐ[k] A ⊗[k] k).comp ε := by ext x; simp
      rw [mul, e₁, one, _root_.mul_one]
      exact cg (by ext x; simp)))
  letI : HopfAlgebra k A := HopfAlgebra.ofAlgHom σ
    (pt_inj h₁ h₂ (by
      refine (mul _).trans (Eq.trans ?_ (one _).symm)
      exact (congrArg₂ (· * ·) ((cg (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _)).trans hσ)
        ((cg (Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _)).trans hid)).trans
        (inv_mul_cancel _)))
    (pt_inj h₁ h₂ (by
      refine (mul _).trans (Eq.trans ?_ (one _).symm)
      exact (congrArg₂ (· * ·) ((cg (Algebra.TensorProduct.lift_comp_includeLeft _ _ fun _ _ => Commute.all _ _)).trans hid)
        ((cg (Algebra.TensorProduct.lift_comp_includeRight _ _ fun _ _ => Commute.all _ _)).trans hσ)).trans
        (mul_inv_cancel _)))
  have hco : Coalgebra.IsCocomm k A := ⟨by
    have : (Algebra.TensorProduct.comm k A A).toAlgHom.comp Δ = Δ := pt_inj h₁ h₂ (by
      rw [mul, hΔ, mul_comm]
      exact congrArg₂ (· * ·) (cg (by ext x; simp)) (cg (by ext x; simp)))
    exact congr(($this).toLinearMap)⟩
  obtain ⟨D, T, h⟩ := assemble bV bU u hf hfi D₀
    (fun i a b => (hD i a b).trans ((add_comm _ _).trans (congrArg₂ (· + ·) rfl rfl))) hli P hP
  exact ⟨A, inferInstance, inferInstance, hco, ‹Module.Finite k A›, rfl, D, T, h⟩

theorem kerHopf_geom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left →
    ∃ (A' : Type) (_ : CommRing A') (_ : HopfAlgebra k A') (_ : Coalgebra.IsCocomm k A') (_ : Module.Finite k A'),
    Module.finrank k A' = Module.finrank k A ∧
    ∃ (D : LinearMap.ker (Matrix.toLin' (rho g.B a)) →ₗ[k] (A' →ₗ[k] k))
    (T : LinearMap.ker (Matrix.toLin' (rho g.B (star a))) →ₗ[k] A'),
    Function.Injective D ∧ Function.Injective T ∧
    (∀ u f f', D u (f * f') = D u f * Coalgebra.counit (R := k) f' + Coalgebra.counit (R := k) f * D u f') ∧
    (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : A') + (1 : A') ⊗ₜ[k] T z) ∧
    ∀ (u : LinearMap.ker (Matrix.toLin' (rho g.B a))) (z : LinearMap.ker (Matrix.toLin' (rho g.B (star a)))),
    (z : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).transpose.mulVec (u : Fin d → k) = 0 → D u (T z) = 0 := by
  intro E _ _ _ H _ hs k _ _ p _ _ t hpr hK d g a A _ _ _ i hp
  have := t.act.hom a
  let V := LinearMap.ker (Matrix.toLin' (rho g.B a))
  let V' := LinearMap.ker (Matrix.toLin' (rho g.B (star a)))
  let bU := Module.finBasis k V
  let bV := Module.finBasis k V'
  have lu : LinearIndependent k fun j => (bU j : Fin d → k) :=
    bU.linearIndependent.map' V.subtype (Submodule.ker_subtype _)
  have lv : LinearIndependent k fun i => (bV i : Fin d → k) :=
    bV.linearIndependent.map' V'.subtype (Submodule.ker_subtype _)
  have hu : ∀ j, (rho g.B a).mulVec (bU j : Fin d → k) = 0 := fun j => by
    have := (bU j).2
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
  have hv : ∀ i, (rho g.B (H.bar a)).mulVec (bV i : Fin d → k) = 0 := fun i => by
    have := (bV i).2
    rwa [LinearMap.mem_ker, Matrix.toLin'_apply, hs] at this
  obtain ⟨κ, h₁, h₂, Δ, e, f, D₀, hΔ, he, hf, hfi, hD, hli, hP⟩ :=
    ker_data E H hs k t hpr hK d g a A i hp _ _ lu lv hu hv
  let P : V →ₗ[k] V' →ₗ[k] k := LinearMap.mk₂ k
    (fun u z => (u : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).mulVec (z : Fin d → k))
    (fun _ _ _ => by simp [add_dotProduct]) (fun _ _ _ => by simp [smul_dotProduct])
    (fun _ _ _ => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun _ _ _ => by simp [Matrix.mulVec_smul, dotProduct_smul])
  obtain ⟨A', i₁, i₂, i₃, i₄, hr, D, T, hDi, hTi, hder, hprim, hpair⟩ :=
    exists_hopf h₁ h₂ Δ hΔ e he bV bU f hf hfi D₀ hD hli P hP
  refine ⟨A', i₁, i₂, i₃, i₄, hr, D, T, hDi, hTi, hder, hprim, fun u z h => ?_⟩
  rw [hpair]
  change (u : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).mulVec (z : Fin d → k) = 0
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  exact h

end GlobalTheory.CompanionTheory.Ar.Flat.KerGeom
end
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperGroupGermFiniteSubschemeStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

theorem _root_.GlobalTheory.T.proper_group_germ_finite_subscheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left →
    ∃ (A' : Type) (_ : CommRing A') (_ : HopfAlgebra k A') (_ : Coalgebra.IsCocomm k A') (_ : Module.Finite k A'),
      Module.finrank k A' = Module.finrank k A ∧
      ∃ (D : LinearMap.ker (Matrix.toLin' (rho g.B a)) →ₗ[k] (A' →ₗ[k] k))
        (T : LinearMap.ker (Matrix.toLin' (rho g.B (star a))) →ₗ[k] A'),
        Function.Injective D ∧ Function.Injective T ∧
        (∀ u f f', D u (f * f') = D u f * Coalgebra.counit (R := k) f' + Coalgebra.counit (R := k) f * D u f') ∧
        (∀ z, Coalgebra.comul (R := k) (T z) = T z ⊗ₜ[k] (1 : A') + (1 : A') ⊗ₜ[k] T z) ∧
        ∀ (u : LinearMap.ker (Matrix.toLin' (rho g.B a))) (z : LinearMap.ker (Matrix.toLin' (rho g.B (star a)))),
          (z : Fin d → k) ⬝ᵥ (bil (g.B.ad a) 1 1).transpose.mulVec (u : Fin d → k) = 0 → D u (T z) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | exact GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.KerGeom.kerHopf_geom <;> assumption)
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernel

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Flat.KerBd

variable {k : Type} [Field k] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

def Wd (B : Germ.FB k d O) (a : O) : Submodule k (Fin d → k) where
  carrier := {u | (rho B a).mulVec u = 0 ∧ ∀ z : Fin d → k, (rho B (star a)).mulVec z = 0 →
      z ⬝ᵥ (bil (B.ad a) 1 1).transpose.mulVec u = 0}
  add_mem' := by
    rintro u v ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    refine ⟨by simp [Matrix.mulVec_add, hu1, hv1], fun z hz => ?_⟩
    simp [Matrix.mulVec_add, dotProduct_add, hu2 z hz, hv2 z hz]
  zero_mem' := ⟨by simp, fun z _ => by simp⟩
  smul_mem' := by
    rintro c u ⟨hu1, hu2⟩
    refine ⟨by simp [Matrix.mulVec_smul, hu1], fun z hz => ?_⟩
    simp [Matrix.mulVec_smul, dotProduct_smul, hu2 z hz]

theorem Wd_le (B : Germ.FB k d O) (a : O) : Wd B a ≤ LinearMap.ker (Matrix.toLin' (rho B a)) :=
  fun u hu => by simpa [Matrix.toLin'_apply] using hu.1

theorem finrank_ker_transpose (M : Matrix (Fin d) (Fin d) k) :
    Module.finrank k (LinearMap.ker (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.ker (Matrix.toLin' M)) := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M)
  have h2 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' M.transpose)
  have h3 : Module.finrank k (LinearMap.range (Matrix.toLin' M.transpose)) =
      Module.finrank k (LinearMap.range (Matrix.toLin' M)) := by
    exact (Matrix.finrank_range_mulVecLin M.transpose).trans ((Matrix.rank_transpose M).trans (Matrix.finrank_range_mulVecLin M).symm)
  omega

theorem finrank_ker_rhoH_le (B : Germ.FB k d O) (a : O) :
    Module.finrank k (LinearMap.ker (rhoH B a)) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)))) + Module.finrank k (Wd B a) := by
  set K := LinearMap.ker (rhoH B a)
  let f : K →ₗ[k] (Fin d → k) := (LinearMap.fst k (Fin d → k) (Fin d → k)).comp K.subtype
  have hrange : LinearMap.range f ≤ Wd B a := by
    rintro _ ⟨y, rfl⟩
    have hy : rhoH B a y = 0 := y.2
    rw [rhoH_apply, Prod.mk_eq_zero] at hy
    refine ⟨hy.1, fun z hz => ?_⟩
    have h2 : (bil (B.ad a) 1 1).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).1 =
        (rho B (star a)).transpose.mulVec (y : (Fin d → k) × (Fin d → k)).2 := (sub_eq_zero.1 hy.2).symm
    simp only [f, LinearMap.comp_apply, Submodule.coe_subtype, LinearMap.fst_apply]
    rw [h2, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, hz, zero_dotProduct]
  let g : LinearMap.ker f →ₗ[k] (Fin d → k) :=
    (LinearMap.snd k (Fin d → k) (Fin d → k)).comp (K.subtype.comp (LinearMap.ker f).subtype)
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have h2 : ((y : K) : (Fin d → k) × (Fin d → k)).2 = 0 := hy
    exact Subtype.ext (Subtype.ext (Prod.ext h1 h2))
  have hgr : LinearMap.range g ≤ LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose) := by
    rintro _ ⟨y, rfl⟩
    have h1 : ((y : K) : (Fin d → k) × (Fin d → k)).1 = 0 := y.2
    have hy : rhoH B a (y : K) = 0 := (y : K).2
    rw [rhoH_apply, Prod.mk_eq_zero, h1] at hy
    simpa [g, Matrix.toLin'_apply] using hy.2
  have e1 := LinearMap.finrank_range_add_finrank_ker f
  have e2 : Module.finrank k (LinearMap.range f) ≤ Module.finrank k (Wd B a) := Submodule.finrank_mono hrange
  have e3 : Module.finrank k (LinearMap.ker f) ≤
      Module.finrank k (LinearMap.ker (Matrix.toLin' (rho B (star a)).transpose)) := by
    rw [← LinearMap.finrank_range_of_inj hg]; exact Submodule.finrank_mono hgr
  rw [finrank_ker_transpose] at e3
  omega

end GlobalTheory.CompanionTheory.Ar.Flat.KerBd

namespace GlobalTheory.CompanionTheory.Ar.Flat


open GlobalTheory.CompanionTheory.Ar.Flat.KerBd in
theorem lemF_ker_order_dvd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  intro E _ _ _ H _ hbar k _ _ p _ _ t hprop hK d g a A _ _ _ i hpb
  obtain ⟨A', _, _, _, _, hrk, D, T, hD, hT, hder, hprim, horth⟩ :=
    GlobalTheory.T.proper_group_germ_finite_subscheme E H hbar k p t hprop hK d g a A i hpb
  let W0 : Submodule k (LinearMap.ker (Matrix.toLin' (rho g.B a))) :=
    (Wd g.B a).comap (LinearMap.ker (Matrix.toLin' (rho g.B a))).subtype
  have hW0 : Module.finrank k W0 = Module.finrank k (Wd g.B a) :=
    (Submodule.comapSubtypeEquivOfLe (Wd_le g.B a)).finrank_eq
  have hc := GlobalTheory.T.primitive_derivation_pairing k p A' (LinearMap.range T) (W0.map D)
    (by rintro _ ⟨z, rfl⟩; exact hprim z)
    (by rintro _ ⟨u, -, rfl⟩; exact hder u)
    (by
      rintro _ ⟨u, hu, rfl⟩ _ ⟨z, rfl⟩
      have hz : (rho g.B (star a)).mulVec (z : Fin d → k) = 0 := by
        have := z.2
        rwa [LinearMap.mem_ker, Matrix.toLin'_apply] at this
      exact horth u z ((hu : (u : Fin d → k) ∈ Wd g.B a).2 z hz))
  rw [LinearMap.finrank_range_of_inj hT, ← (Submodule.equivMapOfInjective D hD W0).finrank_eq, hW0, hrk] at hc
  exact (pow_dvd_pow p (finrank_ker_rhoH_le g.B a)).trans hc

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- Source module: Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProperMultiplicationKernelStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.proper_multiplication_kernel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (t : SAB H (Sp k)), IsProper t.G.hom → Out.KTriv t.G t.PP.L → ∀ (d : ℕ) (g : GermAt t (𝟙 (Sp k)) d) (a : 𝓞 E) (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (i : Sp A ⟶ t.G.left), IsPullback i (spMap (algebraMap k A)) (t.act.act a).left (η[t.G]).left → p ^ Module.finrank k (LinearMap.ker (rhoH g.B a)) ∣ Module.finrank k A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd | exact GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.lemF_ker_order_dvd <;> assumption)
end
end
