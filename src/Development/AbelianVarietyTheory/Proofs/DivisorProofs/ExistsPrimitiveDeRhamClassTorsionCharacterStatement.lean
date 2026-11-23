module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocycleCohomologousOfDeRhamSurjective
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFaithfullyFlatPowEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacter

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDatOfIsAdd

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem exists_dat_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))), CatCoh.H1.mk _ f = c.1 →
    ∀ g : Fn2 A, IsAdd (fv f) g → ∃ d : Dat t c, d.f = f ∧ d.g = g := by
  intro R _ A _ p G t c f hf g hg
  choose liftRes liftRes_spec using fun n ↦ G.res_surjective n
  let value (n : ℕ) : G.A n :=
    fv f (G.A (n + 1)) (G.A n) (G.res n).toAlgHom (t.y (n + 1))
  let h : ∀ n, G.A n := Nat.rec (motive := G.A) 0 (fun n a ↦ liftRes n (a - value n))
  refine ⟨⟨f, hf, g, hg, h, ?_⟩, rfl, rfl⟩
  intro n
  have hres : G.res n (h (n + 1)) = h n - value n := liftRes_spec n _
  change value n = h n - G.res n (h (n + 1))
  rw [hres, sub_sub_cancel]

end GlobalTheory.PtExt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsAddChiEq

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CobChi

theorem exists_isAdd_chi_eq : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (n : ℕ),
    (n : R) = 0 → ∀ (u f : Fn1 A) (g : Fn2 A), IsAdd u g → Cohom (whole A) u f →
    ∃ g' : Fn2 A, IsAdd f g' ∧ ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ n : Pt A D) = 1 → GlobalTheory.PtExt.chi n g' D x = GlobalTheory.PtExt.chi n g D x := by
  intro R _ A _ n hn u f g hu ⟨k, hk⟩
  have hf : ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D')
      (x : Pt A D), f D D' φ x = u D D' φ x - (k D' (spOver φ ≫ x) - φ (k D x)) := by
    intro D _ _ D' _ _ φ x
    have h := hk D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg] at h
    linear_combination -h
  refine ⟨fun D _ _ x y ↦ g D x y - (k D (x * y) - k D x - k D y), ?_, ?_⟩
  · intro D _ _ D' _ _ φ x y
    have h1 := hu D D' φ x y
    simp only [hf, comp_mul, map_sub]
    linear_combination h1
  · intro D _ _ x hx
    have hnD : (n : D) = 0 := by
      rw [← map_natCast (algebraMap R D) n, hn, map_zero]
    have hs : ∑ i ∈ Finset.range n, (k D (x ^ i * x) - k D (x ^ i) - k D x) = 0 := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
      simp_rw [← pow_succ]
      rw [Finset.sum_range_sub (fun i ↦ k D (x ^ i)), hx, pow_zero, sub_self, zero_sub, neg_eq_zero, nsmul_eq_mul,
        hnD, zero_mul]
    simp only [GlobalTheory.PtExt.chi]
    rw [Finset.sum_sub_distrib, hs, sub_zero]

end GlobalTheory.CobChi
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPushoutTorsorNTorsionCharacterStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.T.exists_pushout_torsor_nTorsion_character :
    ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
      (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b →
        ∃ (u : Fn1 A) (g : Fn2 A), IsCoc (whole A) u ∧ IsAdd u g ∧
          ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), (x ^ n : Pt A D) = 1 →
            GlobalTheory.PtExt.chi n g D x = b D x :=
  @GlobalTheory.PtExt.exists_pushout_torsor
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacter

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

theorem GlobalTheory.PtExt.exists_dat_chi_eq (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R]
    (N : ℕ) (hN : (p : R) ^ N = 0) (A : Over (Sp R)) [GrpObj A]
    (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      (x ^ (p ^ N) : Pt A D) = 1 → GlobalTheory.PtExt.chi (p ^ N) d.g D x = b D x := by
  have : IsCommMonObj A := hA.comm
  have hn : ((p ^ N : ℕ) : R) = 0 := by
    simpa only [Nat.cast_pow] using hN
  have hR : GlobalTheory.PtExt.HasRoots A (p ^ N) := fun D _ _ x ↦
    GlobalTheory.PtCover.exists_faithfullyFlat_pow_eq R A hA (p ^ N) (pow_pos (Fact.out : p.Prime).pos N) D x
  obtain ⟨u, g, hu, hg, hchi⟩ := GlobalTheory.T.exists_pushout_torsor_nTorsion_character R A (p ^ N) hn hR b hb
  obtain ⟨f, hf⟩ := GlobalTheory.PtExt.cohom_fv_of_toH1O_surjective R A hs u hu
  obtain ⟨g', hg', hchi'⟩ := GlobalTheory.CobChi.exists_isAdd_chi_eq R A (p ^ N) hn u (fv f) g hg hf
  let c : primDR A := ⟨H1.mk _ f, by rw [show primDR A = ⊤ from hP]; exact Submodule.mem_top⟩
  obtain ⟨d, -, hd⟩ := GlobalTheory.PtExt.exists_dat_of_isAdd R A p G t c f rfl g' hg'
  refine ⟨c, d, fun D _ _ x hx ↦ ?_⟩
  rw [hd, hchi' D x hx, hchi D x hx]
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimitiveDeRhamClassTorsionCharacterStatement

section

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem _root_.GlobalTheory.T.exists_primitive_deRham_class_torsion_character
    (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (N : ℕ) (hN : (p : R) ^ N = 0)
    (A : Over (Sp R)) [GrpObj A] (hA : IsAbelianScheme A) (hP : AllPrim (dp0 R) (𝟙 _) A)
    (hs : Function.Surjective (toH1O (A.hom ≫ 𝟙 _)))
    (G : PDivGroup p R) (t : G.TorsionTower A) (b : Fn0 A) (hb : IsTorsChar (p ^ N) b) :
    ∃ (c : primDR A) (d : Dat t c), ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D),
      x ^ (p ^ N) = 1 → chi (p ^ N) d.g D x = b D x :=
  GlobalTheory.PtExt.exists_dat_chi_eq p R N hN A hA hP hs G t b hb
end
end
