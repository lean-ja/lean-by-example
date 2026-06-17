import fs from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const scriptDir = path.dirname(fileURLToPath(import.meta.url));
const projectRoot = path.resolve(scriptDir, "..");
const bookDir = path.join(projectRoot, "book");
const configPath = path.join(projectRoot, "book.toml");
const sitemapPath = path.join(bookDir, "sitemap.xml");
const sitemapNamespace = "http://www.sitemaps.org/schemas/sitemap/0.9";

const configText = fs.readFileSync(configPath, "utf8");
const siteRoot = ensureTrailingSlash(readTomlString(configText, "site-url"));
const errors = [];

if (!fs.existsSync(bookDir)) {
  fail(`Build directory does not exist: ${bookDir}`);
}

if (!fs.existsSync(sitemapPath)) {
  fail(`Sitemap does not exist: ${sitemapPath}`);
}

const sitemapUrls = readSitemapUrls();
const sitemapSet = new Set(sitemapUrls);
const indexableCanonicalUrls = [];
const noindexPages = [];
const missingCanonicalPages = [];

for (const filePath of findHtmlFiles(bookDir)) {
  const relativePath = toPosixPath(path.relative(bookDir, filePath));
  const html = fs.readFileSync(filePath, "utf8");

  if (relativePath === "404.html" || hasNoindex(html)) {
    noindexPages.push(relativePath);
    continue;
  }

  const canonicalUrl = extractCanonicalUrl(html);
  if (!canonicalUrl) {
    missingCanonicalPages.push(relativePath);
    continue;
  }

  indexableCanonicalUrls.push(canonicalUrl);

  if (!canonicalUrl.startsWith(siteRoot)) {
    errors.push(`${relativePath} has canonical URL outside site-url: ${canonicalUrl}`);
  }
}

const canonicalSet = new Set(indexableCanonicalUrls);
const duplicateSitemapUrls = findDuplicates(sitemapUrls);
const duplicateCanonicalUrls = findDuplicates(indexableCanonicalUrls);
const missingInSitemap = indexableCanonicalUrls.filter((url) => !sitemapSet.has(url));
const extraInSitemap = sitemapUrls.filter((url) => !canonicalSet.has(url));

if (duplicateSitemapUrls.length > 0) {
  errors.push(`sitemap.xml contains duplicate URLs:\n${formatList(duplicateSitemapUrls)}`);
}

if (duplicateCanonicalUrls.length > 0) {
  errors.push(`HTML canonical URLs contain duplicates:\n${formatList(duplicateCanonicalUrls)}`);
}

if (missingCanonicalPages.length > 0) {
  errors.push(`Indexable HTML pages without canonical URL:\n${formatList(missingCanonicalPages)}`);
}

if (missingInSitemap.length > 0) {
  errors.push(`Canonical URLs missing from sitemap.xml:\n${formatList(missingInSitemap)}`);
}

if (extraInSitemap.length > 0) {
  errors.push(`URLs in sitemap.xml without matching indexable canonical URL:\n${formatList(extraInSitemap)}`);
}

if (errors.length > 0) {
  for (const error of errors) {
    console.error(error);
  }
  process.exit(1);
}

console.log(
  `SEO metadata check passed (${indexableCanonicalUrls.length} indexable pages, ${noindexPages.length} noindex pages, ${sitemapUrls.length} sitemap URLs).`,
);

function readSitemapUrls() {
  const xml = fs.readFileSync(sitemapPath, "utf8");

  if (!new RegExp(`<urlset\\s+xmlns=["']${escapeRegExp(sitemapNamespace)}["']`).test(xml)) {
    fail(`sitemap.xml root element must use namespace: ${sitemapNamespace}`);
  }

  const urls = [...xml.matchAll(/<loc>([\s\S]*?)<\/loc>/g)].map((match) =>
    decodeXmlEntities(match[1].trim()),
  );

  if (urls.length === 0) {
    fail("sitemap.xml does not contain any <loc> entries");
  }

  for (const url of urls) {
    if (!url.startsWith(siteRoot)) {
      errors.push(`sitemap.xml contains URL outside site-url: ${url}`);
    }
    if (/\s/.test(url)) {
      errors.push(`sitemap.xml contains URL with whitespace: ${url}`);
    }
  }

  return urls;
}

function readTomlString(text, key) {
  const match = text.match(new RegExp(`^${escapeRegExp(key)}\\s*=\\s*"((?:\\\\.|[^"])*)"`, "m"));
  if (!match) {
    return null;
  }

  return match[1].replace(/\\([btnfr"\\])/g, (_, char) => {
    switch (char) {
      case "b":
        return "\b";
      case "t":
        return "\t";
      case "n":
        return "\n";
      case "f":
        return "\f";
      case "r":
        return "\r";
      case '"':
        return '"';
      case "\\":
        return "\\";
      default:
        return char;
    }
  });
}

function ensureTrailingSlash(url) {
  if (!url) {
    throw new Error('Missing "site-url" in book.toml');
  }

  return url.endsWith("/") ? url : `${url}/`;
}

function findHtmlFiles(dir) {
  const entries = fs.readdirSync(dir, { withFileTypes: true });
  const files = [];

  for (const entry of entries) {
    const entryPath = path.join(dir, entry.name);
    if (entry.isDirectory()) {
      files.push(...findHtmlFiles(entryPath));
    } else if (entry.isFile() && entry.name.endsWith(".html")) {
      files.push(entryPath);
    }
  }

  return files.sort();
}

function toPosixPath(filePath) {
  return filePath.split(path.sep).join("/");
}

function hasNoindex(html) {
  return /<meta\s+name=["']robots["']\s+content=["'][^"']*\bnoindex\b[^"']*["'][^>]*>/i.test(html);
}

function extractCanonicalUrl(html) {
  const match = html.match(/<link\s+rel=["']canonical["'][^>]*href=["']([^"']+)["'][^>]*>/i);
  if (!match) {
    return null;
  }

  return decodeHtmlEntities(match[1]);
}

function decodeHtmlEntities(text) {
  const namedEntities = {
    amp: "&",
    apos: "'",
    gt: ">",
    lt: "<",
    nbsp: " ",
    quot: '"',
  };

  return text.replace(/&(#x[0-9a-fA-F]+|#\d+|[a-zA-Z][a-zA-Z0-9]+);/g, (match, entity) => {
    if (entity.startsWith("#x")) {
      return String.fromCodePoint(Number.parseInt(entity.slice(2), 16));
    }
    if (entity.startsWith("#")) {
      return String.fromCodePoint(Number.parseInt(entity.slice(1), 10));
    }

    return namedEntities[entity] ?? match;
  });
}

function decodeXmlEntities(text) {
  return text
    .replace(/&lt;/g, "<")
    .replace(/&gt;/g, ">")
    .replace(/&quot;/g, '"')
    .replace(/&apos;/g, "'")
    .replace(/&amp;/g, "&");
}

function findDuplicates(values) {
  const seen = new Set();
  const duplicates = new Set();

  for (const value of values) {
    if (seen.has(value)) {
      duplicates.add(value);
    } else {
      seen.add(value);
    }
  }

  return [...duplicates].sort();
}

function formatList(values) {
  const limit = 20;
  const shown = values.slice(0, limit).map((value) => `  - ${value}`);
  const hiddenCount = values.length - shown.length;

  if (hiddenCount > 0) {
    shown.push(`  ... and ${hiddenCount} more`);
  }

  return shown.join("\n");
}

function fail(message) {
  console.error(message);
  process.exit(1);
}

function escapeRegExp(value) {
  return value.replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
}
