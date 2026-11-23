module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusTorsionPointsCorrespondValues
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTensorTorusPointOfComponentTuple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataValuesFactsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceMulStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondencePeriodStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorTorusValueCorrespondenceUniqueComponentsStatement

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGtOver

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor.Vonto

theorem sum_sym_inv {G : Type} [AddCommGroup G] {r : ℕ} (W C : Matrix (Fin r) (Fin r) ℤ)
    (h : (W + W.transpose) * C = 1) (a : Fin r → Fin r → G) :
    ∑ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) = ∑ i, a i i := by
  have e3 : ∀ i k, ∑ j, (W i j + W j i) * C j k = if i = k then 1 else 0 := fun i k => by
    have := congrFun (congrFun h i) k
    rw [Matrix.mul_apply, Matrix.one_apply] at this
    simpa using this
  have e1 : ∀ i, ∑ j, W i j • ((∑ k, C j k • a i k) + ∑ k, C i k • a j k) =
      ∑ j, W i j • ∑ k, C j k • a i k + ∑ j, W i j • ∑ k, C i k • a j k := fun i => by
    rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun j _ => smul_add _ _ _
  rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, W i j • ∑ k, C i k • a j k) = ∑ i, ∑ j, W j i • ∑ k, C j k • a i k from Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  simp_rw [← add_smul, Finset.smul_sum, ← mul_smul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, e3, ite_smul, one_smul, zero_smul]
  simp

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

section Split

variable {X U : Type} [AddCommGroup X] [CommGroup U]

@[ext] structure ExtPt (f : X → X → U) where

  a : X

  u : U

instance (f : X → X → U) : Add (ExtPt f) := ⟨fun p q => ⟨p.a + q.a, p.u * q.u / f p.a q.a⟩⟩

instance (f : X → X → U) : Zero (ExtPt f) := ⟨⟨0, 1⟩⟩

instance (f : X → X → U) : Neg (ExtPt f) := ⟨fun p => ⟨-p.a, f p.a (-p.a) / p.u⟩⟩

def extGroup (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (ExtPt f) where
  add_assoc p q w := by
    refine ExtPt.ext (add_assoc p.a q.a w.a) ?_
    change p.u * q.u / f p.a q.a * w.u / f (p.a + q.a) w.a = p.u * (q.u * w.u / f q.a w.a) / f p.a (q.a + w.a)
    have h := congrArg Additive.ofMul (fc p.a q.a w.a)
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at h ⊢
    linear_combination (norm := abel) -h
  zero_add p := by
    refine ExtPt.ext (zero_add p.a) ?_
    change 1 * p.u / f 0 p.a = p.u
    rw [f0, _root_.one_mul, div_one]
  add_zero p := by
    refine ExtPt.ext (add_zero p.a) ?_
    change p.u * 1 / f p.a 0 = p.u
    rw [fs, f0, _root_.mul_one, div_one]
  neg_add_cancel p := by
    refine ExtPt.ext (neg_add_cancel p.a) ?_
    change f p.a (-p.a) / p.u * p.u / f (-p.a) p.a = 1
    rw [fs (-p.a), div_mul_cancel, div_self']
  add_comm p q := by
    refine ExtPt.ext (add_comm p.a q.a) ?_
    change p.u * q.u / f p.a q.a = q.u * p.u / f q.a p.a
    rw [mul_comm p.u, fs]
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem exists_split [Module.Free ℤ X] (f : X → X → U) (f0 : ∀ a, f 0 a = 1) (fs : ∀ a b, f a b = f b a)
    (fc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) :
    ∃ s : X → U, ∀ a b, s (a + b) * f a b = s a * s b := by
  letI := extGroup f f0 fs fc
  let bX := Module.Free.chooseBasis ℤ X
  let h : X →ₗ[ℤ] ExtPt f := bX.constr ℤ fun i => ⟨bX i, 1⟩
  let p : ExtPt f →ₗ[ℤ] X := AddMonoidHom.toIntLinearMap ⟨⟨ExtPt.a, rfl⟩, fun _ _ => rfl⟩
  have hp : p ∘ₗ h = LinearMap.id := bX.ext fun i => by
    change (h (bX i)).a = bX i
    simp only [h, bX.constr_basis]
  have ha : ∀ x, (h x).a = x := fun x => LinearMap.congr_fun hp x
  refine ⟨fun x => (h x).u, fun a b => ?_⟩
  have e : (h (a + b)).u = (h a).u * (h b).u / f (h a).a (h b).a := congrArg ExtPt.u (map_add h a b)
  show (h (a + b)).u * f a b = (h a).u * (h b).u
  rw [e, ha, ha, div_mul_cancel]

end Split

theorem exists_gt_over {F : Type} [Field F] (N : NumD F) (b : N.A) : ∃ g : N.Gt, g.b = b := by
  obtain ⟨s, hs⟩ := exists_split (fun χ χ' => N.θ (N.c χ) (N.c χ') b)
    (fun a => by rw [N.c_zero, N.cub.face]) (fun a a' => N.cub.s01 _ _ _)
    (fun a a' a'' => by simp only [N.c_add]; exact N.cub.coc _ _ _ _)
  exact ⟨⟨b, s, hs⟩, rfl⟩

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem tor_rel (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det) (t' : Multiplicative N'.X →* Fˣ) :
    ∃ ts : Fin r → (Multiplicative N.X →* Fˣ), GtRelV W φ e wv (N'.tor t') fun j => N.tor (ts j) := by
  obtain ⟨hφm, -, hem, heb, -, -, -, -⟩ := hT
  have hBC : (W + W.transpose) * (W + W.transpose)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  let E : N'.X ≃+ (Fin r → N.X) := AddEquiv.ofBijective (AddMonoidHom.mk' e fun a b => funext (hem a b)) heb
  let sH : Fin r → Multiplicative N.X →* Fˣ := fun k =>
    t'.comp (AddMonoidHom.toMultiplicative ((E.symm : (Fin r → N.X) →+ N'.X).comp (AddMonoidHom.single (fun _ : Fin r => N.X) k)))
  let C : Fin r → Fin r → ℤ := ((W + W.transpose)⁻¹ : Matrix (Fin r) (Fin r) ℤ)
  let M : Fin r → Fin r → ℤ := W
  refine ⟨fun j => ∏ k, sH k ^ C j k, fun j => ?_, fun χ' => ?_⟩
  · have h1 := hφm 1 1 j
    rw [_root_.mul_one] at h1
    exact mul_eq_left.1 h1.symm
  · have hχ : χ' = ∑ i, E.symm (Pi.single i (e χ' i)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, Finset.univ_sum_single]; exact (E.symm_apply_apply χ').symm
    have ht : t' (Multiplicative.ofAdd χ') = ∏ i, sH i (Multiplicative.ofAdd (e χ' i)) := by
      conv_lhs => rw [hχ]
      rw [ofAdd_sum, map_prod]
      rfl
    simp only [NumD.torus_generator_apply, NumD.tor_b, N.cub.face₂, N.cub.face₃, _root_.mul_one, div_one]
    congr 2
    congr 1
    rw [ht]
    change (∏ i, sH i (Multiplicative.ofAdd (e χ' i))) =
      ∏ i, ∏ j, ((∏ k, sH k ^ C j k) (Multiplicative.ofAdd (e χ' i)) *
        (∏ k, sH k ^ C i k) (Multiplicative.ofAdd (e χ' j))) ^ M i j
    have hp (f : Fin r → (Multiplicative N.X →* Fˣ)) (x : Multiplicative N.X) :
        (∏ k, f k) x = ∏ k, f k x := by
      exact map_prod (MonoidHom.eval x) _ _
    simp only [hp, MonoidHom.zpow_apply]
    apply Additive.ofMul.injective
    simp only [ofMul_prod, ofMul_zpow, ofMul_mul]
    exact (sum_sym_inv W C hBC fun i k => Additive.ofMul (sH k (Multiplicative.ofAdd (e χ' i)))).symm

end GlobalTheory.Mum.TensTor.Vonto

namespace GlobalTheory.Mum.TensTor.Vonto

variable {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F}

theorem of_exist_mul (hT : TensFacts W φ e wv) (hdet : IsUnit (W + W.transpose).det)
    (hex : ∀ vs : Fin r → N.Gt, ∃ v' : N'.Gt, GtRelV W φ e wv v' vs)
    (hmul : ∀ (v' u' : N'.Gt) (vs us : Fin r → N.Gt), GtRelV W φ e wv v' vs → GtRelV W φ e wv u' us →
      GtRelV W φ e wv (v' * u') (vs * us))
    (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  choose g hg using fun j => exists_gt_over N (φ v'.b j)
  obtain ⟨u', hu'⟩ := hex g
  have hb : u'.b = v'.b := hT.2.1.1 (funext fun j => (hu'.1 j).trans (hg j))
  obtain ⟨t', ht'⟩ := (N'.exists_tor_iff (u'⁻¹ * v')).2 (by rw [NumD.Gt.mul_b, NumD.Gt.inv_b, hb, inv_mul_cancel])
  obtain ⟨ts, hts⟩ := tor_rel hT hdet t'
  have h := hmul u' (N'.tor t') g (fun j => N.tor (ts j)) hu' hts
  rw [ht', mul_inv_cancel_left] at h
  exact ⟨_, h⟩

end GlobalTheory.Mum.TensTor.Vonto
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensor

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_onto (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F) (hT : TensFacts W φ e wv)
    (hdet : IsUnit (W + W.transpose).det) (v' : N'.Gt) : ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs :=
  Vonto.of_exist_mul hT hdet (VExist.gtRelV_exists F N N' W φ e wv hT)
    (gtRelV_mul F N N' W φ e wv hT) v'

end GlobalTheory.Mum.TensTor
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusComponentsOfUnimodularTensorStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.exists_torus_components_of_unimodular_tensor : ∀ (F : Type) [Field F] (N N' : NumD F) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (φ : N'.A → Fin r → N.A) (e : N'.X → Fin r → N.X) (wv : N'.A → F), TensFacts W φ e wv → IsUnit (W + W.transpose).det → ∀ v' : N'.Gt, ∃ vs : Fin r → N.Gt, GtRelV W φ e wv v' vs := by
  first | exact @GlobalTheory.Mum.TensTor.gtRelV_onto | exact GlobalTheory.Mum.TensTor.gtRelV_onto | (intros; apply GlobalTheory.Mum.TensTor.gtRelV_onto <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodular

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.TensTor

theorem gtRelV_npow_of_tensFacts {F : Type} [Field F] {N N' : NumD F} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
    {φ : N'.A → Fin r → N.A} {e : N'.X → Fin r → N.X} {wv : N'.A → F} (hf : TensFacts W φ e wv)
    {v' : N'.Gt} {vs : Fin r → N.Gt} (h : GtRelV W φ e wv v' vs) (k : ℕ) :
    GtRelV W φ e wv (v' ^ k) (vs ^ k) := by
  induction k with
  | zero =>
    have h0 := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W φ e wv hf 0
    have he0 : ∀ j, e 0 j = 0 := fun j => by
      have := hf.2.2.1 0 0 j
      rw [add_zero] at this
      simpa using this
    have e1 : (1 : Fin r → N.Gt) = fun j => N.io (e 0 j) := funext fun j => by rw [he0, N.io_zero]; rfl
    rw [pow_zero, pow_zero, e1, ← N'.io_zero]
    exact h0
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact GlobalTheory.T.tensorTorusValueCorrespondence_mul F N N' W φ e wv hf _ _ _ _ ih h

theorem exists_components_of_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  intro R _ _ _ hB D D' r W T F _ _ _ N N' ν ν' hW k p'
  have hGt := GlobalTheory.Ex.GtValues.points_correspond
  have hf := GlobalTheory.T.tensorData_values_facts R hB D D' W T F N N' ν ν'
  obtain ⟨q', hq', -⟩ := ((hGt R D'.toPre D'.psi_even D'.tau_bimult F N' ν').2.2.2.2 k).1 p'
  obtain ⟨vs, hvs⟩ := GlobalTheory.T.exists_torus_components_of_unimodular_tensor F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW q'.1.2
  have hk := gtRelV_npow_of_tensFacts hf hvs k
  rw [N'.mem_QT.1 q'.2] at hk
  have hio := GlobalTheory.T.tensorTorusValueCorrespondence_period F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf q'.1.1.toAdd
  have hv := GlobalTheory.T.tensorTorusValueCorrespondence_unique_components F N N' W (cmp T ν ν') (chi T ν ν') (wv T ν ν') hf hW _ _ _ hk hio
  let qs : Fin r → N.QT k := fun j =>
    ⟨(Multiplicative.ofAdd (chi T ν ν' q'.1.1.toAdd j), vs j), N.mem_QT.2 (congrFun hv j)⟩
  choose ps hps using fun j => ((hGt R D.toPre D.psi_even D.tau_bimult F N ν).2.2.2.2 k).2.1 (qs j)
  exact ⟨ps, q', qs, hq', hps, fun _ => rfl, hvs⟩

end GlobalTheory.Mum.TensTor
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentTupleTensorTorsionUnimodularStatement

section

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor


theorem _root_.GlobalTheory.T.exists_component_tuple_tensor_torsion_unimodular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N'), IsUnit (W + W.transpose).det → ∀ (k : ℕ) (p' : QkPt D'.toPre F k), ∃ ps : Fin r → QkPt D.toPre F k, PtRel T ν ν' p' ps := by
  first | exact @GlobalTheory.Mum.TensTor.exists_components_of_unimodular | exact GlobalTheory.Mum.TensTor.exists_components_of_unimodular | (intros; apply GlobalTheory.Mum.TensTor.exists_components_of_unimodular <;> assumption)
end
end
