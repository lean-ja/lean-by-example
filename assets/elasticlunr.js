/**
 * @see https://github.com/HillLiu/docker-mdbook
 */
window.elasticlunr.Index.load = (index) => {
  const FzF = window.fzf.Fzf;
  const storeDocs = index.documentStore.docs;
  const indexArr = Object.keys(storeDocs);
  const ofzf = new FzF(indexArr, {
    selector: (item) => {
      const res = storeDocs[item];
      res.text = `${res.title}${res.breadcrumbs}${res.body}`;
      return res.text;
    },
  });
  return {
    search: (searchterm) => {
      const entries = ofzf.find(searchterm);
      return entries.map((data) => {
        const { item, score } = data;
        return {
          doc: storeDocs[item],
          ref: item,
          score,
        };
      });
    },
  };
};