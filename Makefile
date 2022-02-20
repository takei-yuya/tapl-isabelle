.PHONY: presentation
presentation:
	isabelle build -o browser_info -P build -v -d . tapl-isabelle
	mkdir -p presentation presentation/fonts
	mv build/fonts/* presentation/fonts/
	mv build/Unsorted/tapl-isabelle/* presentation/
	sed "s_url('\.\./\.\./fonts/_url('fonts/_" -i presentation/isabelle.css
	rm presentation/session_graph.pdf
	rm presentation/index.html
	rm -rf build
