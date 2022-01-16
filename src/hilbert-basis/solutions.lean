import tactic
import data.polynomial.degree
import ring_theory.noetherian
import data.polynomial.algebra_map

variables (R : Type) [comm_ring R]

namespace polynomial

noncomputable def filtration (n : ℕ) : submodule R (polynomial R) :=
{ carrier := {f | degree f ≤ n},
  zero_mem' := by simp,
  add_mem' := λ f g hf hg, begin 
    show (f + g).degree ≤ n, -- definitional change -- unnecessary
    change f.degree ≤ n at hf, -- definitional change
    change g.degree ≤ n at hg, -- definitional change
    refine le_trans (degree_add_le f g) _, -- transitivity of ≤
    exact max_le hf hg,
  end,
  smul_mem' := λ c f hc, le_trans (degree_smul_le c f) hc, -- term mode proof
}

noncomputable def proj (n : ℕ) : polynomial R →ₗ[R] R :=
{ to_fun := λ f, coeff f n,
  map_add' := by simp,
  map_smul' := begin
    rintro c f,
    simp,
  end }

-- def filtration.range_mono {a b : ℕ} (h : a ≤ b) :
--   (proj R a).range ≤ (proj R b).range :=
-- begin
--   rcases le_iff_exists_add.1 h with ⟨d, rfl⟩,
--   rintro _ ⟨⟨f, (hf : f.degree ≤ a)⟩, rfl⟩,
--   use f * X^d,
--   { change (f * X^d).degree ≤ a + d,
--     refine le_trans (degree_mul_le _ _) _,
--     exact add_le_add hf (degree_X_pow_le d) },
--   { -- I did some definitional unfolding in Lean then deleted it all
--     -- once I'd found out what the goal actually said
--     exact coeff_mul_X_pow f d a }, 
-- end

theorem hilbert_basis_theorem (hR : is_noetherian_ring R) :
  is_noetherian_ring (polynomial R) :=
begin
  rw is_noetherian_ring_iff_ideal_fg,
  intro I,
  let J : submodule R (polynomial R) := submodule.restrict_scalars R I,
  let F : ℕ → ideal R := λ n, (J ⊓ filtration R n).map (proj R n),
  have F_mono : ∀ {a b}, a ≤ b → F a ≤ F b,
  { intros a b h,
    rw le_iff_exists_add at h,
    rcases h with ⟨c, rfl⟩,
    rintro - ⟨f, ⟨hf1, (hf2 : f.degree ≤ a)⟩, rfl⟩,
    refine ⟨f * X^c, ⟨ideal.mul_mem_right _ I hf1 , _⟩, _⟩,
    { show degree (f * X^c) ≤ a + c,
      refine le_trans (degree_mul_le f _) _,
      refine add_le_add hf2 (degree_X_pow_le c) },
    { change (f * X ^ c).coeff (a + c) = f.coeff a,
      exact coeff_mul_X_pow f c a } },
  let K : ideal R := ⨆ n, F n,
  have hY : submodule.fg K := (is_noetherian_ring_iff_ideal_fg R).1 hR K,
  have hK := submodule.coe_supr_of_directed F
    (λ a b, ⟨max a b, F_mono (le_max_left _ _), F_mono (le_max_right _ _)⟩),
  rw set.ext_iff at hK,
  have hK' : ∀ x ∈ K, ∃ n, x ∈ F n,
  { intros x hx,
    have := (hK x).1 (by simp [hx]),
    rw set.mem_Union at this,
    exact this, }, clear hK,
  cases hY with S hS,
  choose f hf using hK',
  have hS2 : ∀ x, x ∈ S → x ∈ K,
  { intros x hx,
    rw [← hS],
    refine submodule.subset_span hx },
  have hF : ∀ n, submodule.fg (F n),
  { intro n,
    exact (is_noetherian_ring_iff_ideal_fg R).1 hR _ },
  
end

end polynomial