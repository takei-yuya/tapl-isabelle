.PHONY: docs
docs:
	isabelle build -o browser_info -P build -v -d . tapl-isabelle
	mkdir -p docs docs/fonts
	mv build/fonts/* docs/fonts/
	mv build/Unsorted/tapl-isabelle/* docs/
	sed "s_url('\.\./\.\./fonts/_url('fonts/_" -i docs/isabelle.css
	rm -rf build
