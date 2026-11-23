module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmHostUnitAddConjEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivOfIsometryApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModuliOfSignatureEq
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
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicShearOfAdjointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSectionOppositeCongrModStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOpposite

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShear

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem IsOpp.exists_isometry_extend {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ)
    (hN : 0 < N) (Z Z' : Submodule (𝓞 E) D.La) (h : IsOpp D Z Z') (t : Z →ₗ[𝓞 E] D.La)
    (ht : ∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) (hiso : ∀ z z' : Z, D.EF (t z) (t z') = 0) :
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ z : Z, g z = t z := by
  set q := h.symm.proj with hq
  have hr : ∀ a, a - (q a : D.La) ∈ perp D Z' := fun a => h.symm.sub_proj_mem a
  have hδ : ∀ z : Z, t z - (z : D.La) ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hz⟩ := ht z
    rw [hz, add_sub_cancel_left]
    exact nsmul_mem he N
  choose c hc hu using fun a : D.La => h.2.2.1 (AddMonoidHom.mk' (fun z : Z => D.EF (t z - z) (a - q a))
    fun z z' => by simp only [map_add (f := _), map_sub, Submodule.coe_add, LinearMap.add_apply, LinearMap.sub_apply]; abel)
  simp only [AddMonoidHom.mk'_apply] at hc hu
  let α : D.La →ₗ[𝓞 E] Z' :=
    { toFun := c
      map_add' := fun a a' => (hu _ _ fun z => by
        simp only [Submodule.coe_add, map_add (f := _), hc, map_sub, LinearMap.sub_apply, map_add (f := _)]
        abel).symm
      map_smul' := fun x a => (hu _ _ fun z => by
        have key : ∀ u w : D.La, D.EF u (x • w) = D.EF (H.bar x • u) w := fun u w => by rw [D.adj, bar_bar]
        simp only [RingHom.id_apply, Submodule.coe_smul, map_smul, ← smul_sub]
        rw [key, key, ← Submodule.coe_smul, hc, Submodule.coe_smul, map_smul, smul_sub]).symm }
  have hα : ∀ a, α a = c a := fun _ => rfl
  let g : D.La →ₗ[𝓞 E] D.La := LinearMap.id + (t - Z.subtype) ∘ₗ q - Z'.subtype ∘ₗ α
  have hg : ∀ a, g a = a + (t (q a) - q a) - c a := fun _ => rfl
  refine ⟨g, fun a a' => ?_, fun a => ?_, fun z => ?_⟩
  · have hZ : ∀ (x y : Z), D.EF x y = 0 := fun x y => h.1 x.2 _ y.2
    have hZ' : ∀ (x y : Z'), D.EF x y = 0 := fun x y => h.2.1 x.2 _ y.2
    have f1 := hZ' (c a) (c a')
    have f2 : D.EF (t (q a) - q a) (c a') = 0 := hδ (q a) _ (c a').2
    have f3 : D.EF (c a) (t (q a') - q a') = 0 := by
      rw [ef_swap, hδ (q a') _ (c a).2, neg_zero]
    have f4 := hiso (q a) (q a')
    have f5 := hZ (q a) (q a')
    have f7 : D.EF a (c a') = D.EF (t (q a) - q a) (a' - q a') := by
      have := hr a _ (c a').2
      rw [← hc a' (q a)]
      simp only [map_sub, LinearMap.sub_apply] at this
      linear_combination this
    have f8 : D.EF (c a) a' = D.EF (a - q a) (t (q a') - q a') := by
      have := hr a' _ (c a).2
      have h2 := hc a (q a')
      rw [ef_swap D (c a) a', ef_swap D (a - q a)]
      simp only [map_sub, LinearMap.sub_apply] at this h2 ⊢
      linear_combination -this - h2
    rw [hg, hg]
    simp only [map_add (f := _), map_sub, LinearMap.add_apply, LinearMap.sub_apply] at f2 f3 f7 f8 ⊢
    linear_combination f1 - f2 - f3 + f4 - f5 - f7 - f8
  · obtain ⟨e, -, he⟩ := ht (q a)
    obtain ⟨e', he'⟩ := GlobalTheory.ModuliGenus.exists_eq_nsmul_of_dvd D hN (c a : D.La) fun b => by
      obtain ⟨e₁, -, he₁⟩ := ht (q b)
      have h1 : D.EF (c a) (b - q b) = 0 := by rw [ef_swap, hr b _ (c a).2, neg_zero]
      have h2 := hc a (q b)
      rw [he₁, add_sub_cancel_left, map_nsmul, LinearMap.smul_apply] at h2
      refine ⟨-D.EF e₁ (a - q a), ?_⟩
      have h3 : D.EF (c a) b = D.EF (c a) (q b) := by
        rw [map_sub] at h1; linear_combination h1
      rw [h3, ef_swap, h2, nsmul_eq_mul]
      ring
    refine ⟨e - e', ?_⟩
    rw [hg, he, he', smul_sub]
    abel
  · have hqz : q z = z := Subtype.ext (h.symm.proj_of_mem z.2)
    have hcz : c z = 0 := (hu z 0 fun z' => by simp [hqz]).symm
    rw [hg, hqz, hcz]
    simp

end GlobalTheory.LowFilt
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryExtendingIsotropicShearStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.exists_isometry_extending_isotropic_shear : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (N : ℕ), 0 < N → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' → ∀ t : Z →ₗ[𝓞 E] D.La,
    (∀ z : Z, ∃ e ∈ perp D Z', t z = (z : D.La) + N • e) → (∀ z z' : Z, D.EF (t z) (t z') = 0) →
    ∃ g : D.La →ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧ ∀ z : Z, g z = t z := by
  first | exact @GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | exact GlobalTheory.LowFilt.IsOpp.exists_isometry_extend | (intros; apply GlobalTheory.LowFilt.IsOpp.exists_isometry_extend <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveModOfSurjectiveModOppositeStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.injective_mod_of_surjective_mod_opposite : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X → (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∀ b ∈ Z', (∃ e, y b = n • e) → ∃ e ∈ Z', b = n • e := by
  first | exact @GlobalTheory.LowFilt.inj_mod_of_surj_mod | exact GlobalTheory.LowFilt.inj_mod_of_surj_mod | (intros; apply GlobalTheory.LowFilt.inj_mod_of_surj_mod <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmul

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

namespace GlobalTheory.LowFilt

theorem ker_mod_eq_perp_range_add : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ y n hn Z Z' h hsurj t ht hiso hdiv a
  have hW : IsOpp D (LinearMap.range t) Z' := (h.symm.shear t ht hiso).symm

  have hdivZ : ∀ b ∈ Z', (∀ z : Z, (n : ℤ) ∣ D.EF (t z) b) → ∃ b'', b = n • b'' := by
    intro b hb hbd
    have hx : ∀ x : LinearMap.range t, (n : ℤ) ∣ D.EF x b := by
      rintro ⟨_, z, rfl⟩
      exact hbd z
    let φ : LinearMap.range t →+ ℤ := AddMonoidHom.mk' (fun x => D.EF x b / n) fun x x' => by
      simp only [Submodule.coe_add, map_add (f := _), LinearMap.add_apply]
      exact Int.add_ediv_of_dvd_left (hx x)
    obtain ⟨b'', hb'', -⟩ := hW.2.2.1 φ
    refine ⟨b'', ?_⟩
    have h0 : (n • (b'' : D.La)) - b = 0 := by
      refine hW.eq_zero (sub_mem (Z'.nsmul_mem b''.2 n) hb) fun w hw => ?_
      have e1 := hb'' ⟨w, hw⟩
      simp only [φ, AddMonoidHom.mk'_apply] at e1
      have e2 : (n : ℤ) ∣ D.EF w b := hx ⟨w, hw⟩
      rw [ef_swap, map_sub, map_nsmul, e1, nsmul_eq_mul, Int.mul_ediv_cancel' e2]
      simp
    exact (sub_eq_zero.1 h0).symm
  have hperp0 : ∀ (k : D.La), k ∈ perp D (LinearMap.range t) → ∀ z : Z, D.EF (t z) k = 0 := by
    intro k hk z
    rw [ef_swap, hk _ ⟨z, rfl⟩, neg_zero]
  constructor
  · rintro ⟨e, he⟩
    obtain ⟨b, hb, hk⟩ := hW.exists_sub_mem_perp a
    obtain ⟨b'', hb''⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z a ⟨e, he⟩
      have h2 : D.EF (t z) b = D.EF (t z) a - D.EF (t z) (a - b) := by
        rw [map_sub]; ring
      rw [h2, hperp0 _ hk z, sub_zero]
      exact h1
    refine ⟨a - b, hk, b'', ?_⟩
    rw [← hb'', sub_add_cancel]
  · rintro ⟨k, hk, e, rfl⟩
    obtain ⟨b, hb, e₁, hb1⟩ := hsurj (y k)
    obtain ⟨b'', rfl⟩ := hdivZ b hb fun z => by
      have h1 := hdiv z (k - b) ⟨-e₁, by rw [map_sub, hb1, smul_neg]; abel⟩
      rw [map_sub, hperp0 _ hk z, zero_sub, Int.dvd_neg] at h1
      exact h1
    refine ⟨y b'' - e₁ + y e, ?_⟩
    rw [map_nsmul] at hb1
    rw [map_add (f := _), map_nsmul, smul_add, smul_sub, hb1]
    abel

end GlobalTheory.LowFilt
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerModEqOrthogonalRangeShearAddNsmulStatement

section

@[expose] public section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem _root_.GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
    (y : D.La →ₗ[𝓞 E] X) (n : ℕ), 0 < n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) → ∀ t : Z →ₗ[𝓞 E] D.La, (∀ z : Z, t z - z ∈ perp D Z') →
    (∀ z z' : Z, D.EF (t z) (t z') = 0) → (∀ (z : Z) (a : D.La), (∃ e, y a = n • e) → (n : ℤ) ∣ D.EF (t z) a) →
    ∀ a, (∃ e, y a = n • e) ↔ ∃ b ∈ perp D (LinearMap.range t), ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | exact GlobalTheory.LowFilt.ker_mod_eq_perp_range_add | (intros; apply GlobalTheory.LowFilt.ker_mod_eq_perp_range_add <;> assumption)
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicMod

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.exists_isometry_kerIs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n N hn hNn hC Z Z' h hrk hN hon
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  have hinj := GlobalTheory.T.injective_mod_of_surjective_mod_opposite D y n hn Z Z' h hrk hon
  obtain ⟨σ, hσZ', hσid, hσy, hσN⟩ := GlobalTheory.T.exists_linear_section_opposite_congr_mod D y n N hn hNn Z Z' h hN hon
  obtain ⟨w, hw⟩ := exists_adjoint D σ
  obtain ⟨t, ht, hiso, hdvd⟩ := GlobalTheory.T.exists_isotropic_shear_of_adjoint D y n N hn hNn hC Z Z' h σ w hσZ' hσid hσy hσN hw hinj
  have ht' : ∀ z : Z, t z - z ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hze⟩ := ht z
    rw [hze, add_sub_cancel_left]
    exact (perp D Z').nsmul_mem he N
  have hker := GlobalTheory.T.ker_mod_eq_orthogonal_range_shear_add_nsmul D y n hn Z Z' h hon t ht' hiso hdvd
  obtain ⟨g, hg, hgN, hgt⟩ := GlobalTheory.T.exists_isometry_extending_isotropic_shear D N hN0 Z Z' h t ht hiso
  refine ⟨equivOfIsometry D g hg, hg, hgN, fun a => ?_⟩
  simp only [equivOfIsometry_apply]
  rw [hker (g a)]
  constructor
  · rintro ⟨b, hb, e, he⟩
    set G := equivOfIsometry D g hg
    have hG : ∀ x, G x = g x := fun x => rfl
    refine ⟨G.symm b, fun z hz => ?_, G.symm e, ?_⟩
    · have := hb (t ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩
      rw [← hgt ⟨z, hz⟩, ← G.apply_symm_apply b, hG, hg] at this
      exact this
    · apply G.injective
      rw [map_add (f := _), map_nsmul, G.apply_symm_apply, G.apply_symm_apply, hG, he]
  · rintro ⟨b, hb, e, rfl⟩
    refine ⟨g b, ?_, g e, by rw [map_add (f := _), map_nsmul]⟩
    rintro _ ⟨z, rfl⟩
    rw [← hgt z, hg]
    exact hb z z.2
end
end
end

-- Source module: Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicModStatement

section

@[expose] public section

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt


theorem _root_.GlobalTheory.T.exists_isometry_kernel_coisotropic_mod : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  first | exact @GlobalTheory.LowFilt.exists_isometry_kerIs | exact GlobalTheory.LowFilt.exists_isometry_kerIs | (intros; apply GlobalTheory.LowFilt.exists_isometry_kerIs <;> assumption)
end
end
end
