-- Highest priority: a program is one long line, which LazyVim's bigfile check claims
-- for itself, and then the plugin never loads.
vim.filetype.add({ pattern = { [".*%.emd"] = { "emd", { priority = math.huge } } } })
